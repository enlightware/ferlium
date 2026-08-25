use std::{
    fs::{self, OpenOptions, TryLockError},
    io::Write,
    path::{Path, PathBuf},
    sync::atomic::{AtomicU64, Ordering},
    thread,
    time::{Duration, Instant},
};

use crate::{
    SourceTable,
    compiler::{CompilerSession, MirArtifacts, Modules},
    module::Module,
};
use directories::ProjectDirs;
use sha2::{Digest, Sha256};

use super::{CompiledStdMirSnapshot, CompiledStdSnapshot, MirSnapshotStage};

const LOCK_POLL_INTERVAL: Duration = Duration::from_millis(20);
const LOCK_WAIT_LIMIT: Duration = Duration::from_secs(120);
static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);
const CACHE_MAGIC: &[u8; 8] = b"FERSTD\0\x01";
const CHECKSUM_LEN: usize = 32;
type CacheChecksum = [u8; CHECKSUM_LEN];
type CachedStd = (SourceTable, Module, Option<CacheChecksum>);
type CachedMir = (MirArtifacts, Option<CacheChecksum>);

struct CheckedPayload<'a> {
    payload: &'a [u8],
    checksum: [u8; CHECKSUM_LEN],
}

/// Load compiled std from the process-shared cache, or build and atomically publish it once.
/// Every cache/IO/decoding failure is a miss; compiler startup must remain reliable.
pub(crate) fn load_or_build_std() -> CachedStd {
    let Some(cache_path) = cache_path() else {
        return compile_without_cache();
    };
    if let Ok(Some(restored)) = try_load(&cache_path) {
        return restored;
    }
    let failure_path = cache_path.with_extension("invalid");
    if failure_path.exists() {
        return compile_without_cache();
    }
    if fs::create_dir_all(cache_path.parent().expect("cache file has a parent")).is_err() {
        return compile_without_cache();
    }

    let lock_path = cache_path.with_extension("lock");
    let Ok(lock_file) = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(lock_path)
    else {
        return compile_without_cache();
    };
    let started = Instant::now();
    loop {
        if failure_path.exists() {
            return compile_without_cache();
        }
        if let Ok(Some(restored)) = try_load(&cache_path) {
            return restored;
        }
        match lock_file.try_lock() {
            Ok(()) => {
                // Another writer may have won between our optimistic read and lock acquisition.
                match try_load(&cache_path) {
                    Ok(Some(restored)) => return restored,
                    Ok(None) => {}
                    Err(error) => {
                        log::warn!(
                            "discarding unusable compiled std cache {}: {error}",
                            cache_path.display()
                        );
                        let _ = fs::remove_file(&cache_path);
                    }
                }
                invalidate_mir_from(&cache_path, MirSnapshotStage::Raw);
                let (snapshot, module) = match CompiledStdSnapshot::capture() {
                    Ok(captured) => captured,
                    Err(failure) => {
                        let error = failure.error().to_string();
                        log::warn!("failed to capture compiled std snapshot: {error}");
                        mark_cache_unusable(&failure_path, &error);
                        let (sources, module) = failure.into_compiled_std();
                        return (sources, module, None);
                    }
                };
                let payload = match snapshot.encode() {
                    Ok(payload) => payload,
                    Err(error) => {
                        log::warn!("failed to encode compiled std snapshot: {error}");
                        return (snapshot.captured_sources(), module, None);
                    }
                };
                let restored = match validate_payload(&payload) {
                    Ok(restored) => restored,
                    Err(error) => {
                        log::warn!(
                            "compiled std snapshot failed validation and will not be cached: {error}"
                        );
                        mark_cache_unusable(&failure_path, &error);
                        return (snapshot.captured_sources(), module, None);
                    }
                };
                let checksum = payload_checksum(&payload);
                let cache_bytes = cache_file_bytes_with_checksum(&payload, &checksum);
                let checksum = match publish_atomically(&cache_path, &cache_bytes) {
                    Ok(()) => Some(checksum),
                    Err(error) => {
                        log::warn!(
                            "failed to publish compiled std cache {}: {error}",
                            cache_path.display()
                        );
                        None
                    }
                };
                return (restored.0, restored.1, checksum);
            }
            Err(TryLockError::WouldBlock) => {
                if started.elapsed() >= LOCK_WAIT_LIMIT {
                    return compile_without_cache();
                }
                thread::sleep(LOCK_POLL_INTERVAL);
            }
            Err(TryLockError::Error(_)) => return compile_without_cache(),
        }
    }
}

pub(crate) fn load_or_build_raw_std_mir(
    module: &Module,
    modules: &Modules,
    semantic_checksum: Option<[u8; CHECKSUM_LEN]>,
) -> CachedMir {
    let Some(semantic_checksum) = semantic_checksum else {
        return (MirArtifacts::build(module, modules), None);
    };
    load_or_build_mir(
        MirSnapshotStage::Raw,
        semantic_checksum,
        module,
        modules,
        None,
        || MirArtifacts::build(module, modules),
    )
}

pub(crate) fn load_or_build_optimized_std_mir(
    raw: &MirArtifacts,
    raw_checksum: Option<[u8; CHECKSUM_LEN]>,
    module: &Module,
    session: &CompilerSession,
) -> MirArtifacts {
    let Some(raw_checksum) = raw_checksum else {
        return MirArtifacts::optimize(raw, module, session);
    };
    load_or_build_mir(
        MirSnapshotStage::Optimized,
        raw_checksum,
        module,
        session.raw_modules(),
        Some(raw),
        || MirArtifacts::optimize(raw, module, session),
    )
    .0
}

fn load_or_build_mir(
    stage: MirSnapshotStage,
    parent_checksum: [u8; CHECKSUM_LEN],
    module: &Module,
    modules: &Modules,
    raw: Option<&MirArtifacts>,
    build: impl FnOnce() -> MirArtifacts,
) -> CachedMir {
    let Some(semantic_path) = cache_path() else {
        return (build(), None);
    };
    let stage_path = mir_cache_path(&semantic_path, stage);
    let failure_path = stage_path.with_extension("invalid");
    let mut build = Some(build);
    let mut build_now = || (build.take().expect("MIR builder is called once")(), None);
    match try_load_mir(&stage_path, stage, &parent_checksum, module, modules, raw) {
        Ok(Some(restored)) => return restored,
        Ok(None) => {}
        Err(error) => {
            log::warn!(
                "discarding unusable cached {stage:?} std MIR {}: {error}",
                stage_path.display()
            );
            invalidate_mir_from(&semantic_path, stage);
        }
    }
    if failure_path.exists() {
        return build_now();
    }
    if fs::create_dir_all(semantic_path.parent().expect("cache file has a parent")).is_err() {
        return build_now();
    }

    let lock_path = stage_path.with_extension("lock");
    let Ok(lock_file) = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .open(lock_path)
    else {
        return build_now();
    };
    let started = Instant::now();
    loop {
        if failure_path.exists() {
            return build_now();
        }
        if let Ok(Some(restored)) =
            try_load_mir(&stage_path, stage, &parent_checksum, module, modules, raw)
        {
            return restored;
        }
        match lock_file.try_lock() {
            Ok(()) => {
                match try_load_mir(&stage_path, stage, &parent_checksum, module, modules, raw) {
                    Ok(Some(restored)) => return restored,
                    Ok(None) => {}
                    Err(error) => {
                        log::warn!(
                            "discarding unusable cached {stage:?} std MIR {}: {error}",
                            stage_path.display()
                        );
                        invalidate_mir_from(&semantic_path, stage);
                    }
                }

                let (artifacts, _) = build_now();
                let snapshot =
                    match CompiledStdMirSnapshot::capture(stage, parent_checksum, &artifacts) {
                        Ok(snapshot) => snapshot,
                        Err(error) => {
                            let error = error.to_string();
                            log::warn!("failed to capture {stage:?} std MIR snapshot: {error}");
                            mark_cache_unusable(&failure_path, &error);
                            return (artifacts, None);
                        }
                    };
                let payload = match snapshot.encode() {
                    Ok(payload) => payload,
                    Err(error) => {
                        log::warn!("failed to encode {stage:?} std MIR snapshot: {error}");
                        return (artifacts, None);
                    }
                };
                let restored = match restore_mir_snapshot(
                    &snapshot,
                    stage,
                    &parent_checksum,
                    module,
                    modules,
                    raw,
                    true,
                ) {
                    Ok(restored) => restored,
                    Err(error) => {
                        let error = error.to_string();
                        log::warn!("fresh {stage:?} std MIR snapshot is invalid: {error}");
                        mark_cache_unusable(&failure_path, &error);
                        return (artifacts, None);
                    }
                };
                let checksum = payload_checksum(&payload);
                let cache_bytes = cache_file_bytes_with_checksum(&payload, &checksum);
                let checksum = match publish_atomically(&stage_path, &cache_bytes) {
                    Ok(()) => Some(checksum),
                    Err(error) => {
                        log::warn!(
                            "failed to publish {stage:?} std MIR cache {}: {error}",
                            stage_path.display()
                        );
                        None
                    }
                };
                return (restored, checksum);
            }
            Err(TryLockError::WouldBlock) => {
                if started.elapsed() >= LOCK_WAIT_LIMIT {
                    return build_now();
                }
                thread::sleep(LOCK_POLL_INTERVAL);
            }
            Err(TryLockError::Error(_)) => return build_now(),
        }
    }
}

fn compile_without_cache() -> CachedStd {
    let mut sources = SourceTable::default();
    let module = crate::std::std_module(&mut sources);
    (sources, module, None)
}

fn try_load(path: &Path) -> Result<Option<CachedStd>, String> {
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(format!("failed to read cache: {error}")),
    };
    let checked = checked_payload(&bytes).map_err(str::to_owned)?;
    let snapshot = CompiledStdSnapshot::decode(checked.payload)
        .map_err(|error| format!("failed to decode snapshot: {error}"))?;
    snapshot
        .restore()
        .map(|(sources, module)| Some((sources, module, Some(checked.checksum))))
        .map_err(|error| format!("failed to restore snapshot: {error}"))
}

fn try_load_mir(
    path: &Path,
    stage: MirSnapshotStage,
    parent_checksum: &[u8; CHECKSUM_LEN],
    module: &Module,
    modules: &Modules,
    raw: Option<&MirArtifacts>,
) -> Result<Option<CachedMir>, String> {
    let bytes = match fs::read(path) {
        Ok(bytes) => bytes,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(format!("failed to read cache: {error}")),
    };
    let checked = checked_payload(&bytes).map_err(str::to_owned)?;
    let snapshot = CompiledStdMirSnapshot::decode(checked.payload)
        .map_err(|error| format!("failed to decode snapshot: {error}"))?;
    restore_mir_snapshot(
        &snapshot,
        stage,
        parent_checksum,
        module,
        modules,
        raw,
        false,
    )
    .map(|artifacts| Some((artifacts, Some(checked.checksum))))
    .map_err(|error| format!("failed to restore snapshot: {error}"))
}

fn restore_mir_snapshot(
    snapshot: &CompiledStdMirSnapshot,
    stage: MirSnapshotStage,
    parent_checksum: &[u8; CHECKSUM_LEN],
    module: &Module,
    modules: &Modules,
    raw: Option<&MirArtifacts>,
    verify: bool,
) -> Result<MirArtifacts, super::SnapshotError> {
    snapshot.validate_lineage(stage, parent_checksum)?;
    match stage {
        MirSnapshotStage::Raw if verify => snapshot.restore_raw_verified(module, modules),
        MirSnapshotStage::Raw => snapshot.restore_raw(module, modules),
        MirSnapshotStage::Optimized if verify => snapshot.restore_optimized_verified(
            module,
            modules,
            raw.expect("optimized MIR restoration requires raw MIR"),
        ),
        MirSnapshotStage::Optimized => snapshot.restore_optimized(
            module,
            modules,
            raw.expect("optimized MIR restoration requires raw MIR"),
        ),
    }
}

fn validate_payload(payload: &[u8]) -> Result<(SourceTable, Module), String> {
    let snapshot = CompiledStdSnapshot::decode(payload)
        .map_err(|error| format!("failed to decode freshly encoded snapshot: {error}"))?;
    snapshot
        .restore()
        .map_err(|error| format!("failed to restore freshly encoded snapshot: {error}"))
}

fn mark_cache_unusable(path: &Path, error: &str) {
    if let Err(write_error) = fs::write(path, error) {
        log::warn!(
            "failed to record unusable compiled std cache marker {}: {write_error}",
            path.display()
        );
    }
}

#[cfg(test)]
fn cache_file_bytes(payload: &[u8]) -> Vec<u8> {
    let checksum = payload_checksum(payload);
    cache_file_bytes_with_checksum(payload, &checksum)
}

fn cache_file_bytes_with_checksum(payload: &[u8], checksum: &[u8; CHECKSUM_LEN]) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(CACHE_MAGIC.len() + CHECKSUM_LEN + payload.len());
    bytes.extend_from_slice(CACHE_MAGIC);
    bytes.extend_from_slice(checksum);
    bytes.extend_from_slice(payload);
    bytes
}

fn payload_checksum(payload: &[u8]) -> [u8; CHECKSUM_LEN] {
    Sha256::digest(payload).into()
}

fn checked_payload(bytes: &[u8]) -> Result<CheckedPayload<'_>, &'static str> {
    let payload_start = CACHE_MAGIC.len() + CHECKSUM_LEN;
    if bytes.len() < payload_start || &bytes[..CACHE_MAGIC.len()] != CACHE_MAGIC {
        return Err("cache header is missing or invalid");
    }
    let expected = &bytes[CACHE_MAGIC.len()..payload_start];
    let payload = &bytes[payload_start..];
    if Sha256::digest(payload)
        .iter()
        .copied()
        .eq(expected.iter().copied())
    {
        let mut checksum = [0; CHECKSUM_LEN];
        checksum.copy_from_slice(expected);
        Ok(CheckedPayload { payload, checksum })
    } else {
        Err("cache payload checksum does not match")
    }
}

fn mir_cache_path(semantic_path: &Path, stage: MirSnapshotStage) -> PathBuf {
    match stage {
        MirSnapshotStage::Raw => semantic_path.with_extension("raw-mir.bin"),
        MirSnapshotStage::Optimized => semantic_path.with_extension("optimized-mir.bin"),
    }
}

fn invalidate_mir_from(semantic_path: &Path, stage: MirSnapshotStage) {
    // Invalid markers are only retry suppressors. A racing deletion can cause one redundant
    // rebuild, but cannot admit an artifact because lineage and payload checks still run.
    let stages: &[MirSnapshotStage] = match stage {
        MirSnapshotStage::Raw => &[MirSnapshotStage::Raw, MirSnapshotStage::Optimized],
        MirSnapshotStage::Optimized => &[MirSnapshotStage::Optimized],
    };
    for &stage in stages {
        let path = mir_cache_path(semantic_path, stage);
        let _ = fs::remove_file(&path);
        let _ = fs::remove_file(path.with_extension("invalid"));
    }
}

fn cache_path() -> Option<PathBuf> {
    if std::env::var_os("FERLIUM_STD_CACHE_DISABLE").is_some() {
        return None;
    }
    let directory = std::env::var_os("FERLIUM_STD_CACHE_DIR")
        .map(PathBuf::from)
        .or_else(|| {
            ProjectDirs::from("com", "Enlightware", "Ferlium")
                .map(|directories| directories.cache_dir().join("compiled-std"))
        })?;
    Some(directory.join(format!(
        "std-v{}-{}-{}.bin",
        super::STD_SNAPSHOT_FORMAT_VERSION,
        env!("FERLIUM_STD_SOURCE_FINGERPRINT"),
        env!("FERLIUM_SEMANTIC_BUILD_FINGERPRINT"),
    )))
}

fn publish_atomically(path: &Path, bytes: &[u8]) -> std::io::Result<()> {
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let temp = path.with_extension(format!("tmp-{}-{sequence}", std::process::id()));
    let result = (|| {
        let mut file = OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temp)?;
        file.write_all(bytes)?;
        file.sync_all()?;
        match fs::rename(&temp, path) {
            Ok(()) => Ok(()),
            Err(error) if path.exists() => {
                // Windows does not replace an existing destination. The cache lock serializes
                // writers, and readers treat this small replacement window as a miss and wait.
                fs::remove_file(path)?;
                fs::rename(&temp, path).map_err(|_| error)
            }
            Err(error) => Err(error),
        }
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temp);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn atomic_publication_never_exposes_partial_bytes() {
        let directory = std::env::temp_dir().join(format!(
            "ferlium-cache-test-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("snapshot.bin");
        let bytes = vec![0x5a; 128 * 1024];
        publish_atomically(&path, &bytes).unwrap();
        assert_eq!(fs::read(&path).unwrap(), bytes);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn cache_file_checksum_rejects_corruption() {
        let payload = b"snapshot payload";
        let mut bytes = cache_file_bytes(payload);
        let checked = checked_payload(&bytes).unwrap();
        assert_eq!(checked.payload, payload);
        assert_eq!(checked.checksum, Sha256::digest(payload).as_slice());
        *bytes.last_mut().unwrap() ^= 1;
        assert!(matches!(
            checked_payload(&bytes),
            Err("cache payload checksum does not match")
        ));
    }

    #[test]
    fn malformed_cache_is_distinguished_from_a_missing_cache() {
        let directory = std::env::temp_dir().join(format!(
            "ferlium-invalid-cache-test-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("snapshot.bin");
        fs::write(&path, b"not a compiled std snapshot").unwrap();

        assert!(try_load(&directory.join("missing.bin")).unwrap().is_none());
        assert!(
            try_load(&path)
                .unwrap_err()
                .contains("cache header is missing or invalid")
        );
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn invalidation_cascades_only_to_dependent_mir_stages() {
        let directory = std::env::temp_dir().join(format!(
            "ferlium-lineage-test-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        let semantic = directory.join("std.bin");
        fs::write(&semantic, b"semantic").unwrap();
        for stage in [MirSnapshotStage::Raw, MirSnapshotStage::Optimized] {
            let path = mir_cache_path(&semantic, stage);
            fs::write(&path, b"mir").unwrap();
            fs::write(path.with_extension("invalid"), b"failure").unwrap();
        }

        invalidate_mir_from(&semantic, MirSnapshotStage::Optimized);
        assert!(semantic.exists());
        assert!(mir_cache_path(&semantic, MirSnapshotStage::Raw).exists());
        assert!(!mir_cache_path(&semantic, MirSnapshotStage::Optimized).exists());

        invalidate_mir_from(&semantic, MirSnapshotStage::Raw);
        assert!(semantic.exists());
        assert!(!mir_cache_path(&semantic, MirSnapshotStage::Raw).exists());
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn process_lock_is_released_with_its_file_handle() {
        let directory = std::env::temp_dir().join(format!(
            "ferlium-lock-test-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir_all(&directory).unwrap();
        let path = directory.join("snapshot.lock");
        let open = || {
            OpenOptions::new()
                .read(true)
                .write(true)
                .create(true)
                .truncate(false)
                .open(&path)
                .unwrap()
        };
        let owner = open();
        let contender = open();
        owner.try_lock().unwrap();
        assert!(matches!(
            contender.try_lock(),
            Err(TryLockError::WouldBlock)
        ));
        drop(owner);
        contender.try_lock().unwrap();
        drop(contender);
        fs::remove_dir_all(directory).unwrap();
    }

    #[test]
    fn process_shared_cache_restores_a_complete_std() {
        let (first_sources, first, first_checksum) = load_or_build_std();
        let (second_sources, second, second_checksum) = load_or_build_std();

        assert_eq!(second_checksum, first_checksum);
        assert_eq!(second_sources.len(), first_sources.len());
        assert_eq!(second.functions.len(), first.functions.len());
        assert_eq!(second.hir_arena.len(), first.hir_arena.len());
        assert_eq!(second.impls.data.len(), first.impls.data.len());
    }
}
