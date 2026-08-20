use std::collections::BTreeMap;

use crate::{
    std::{buffer::buffer_bare_native_type, hash, math, string},
    types::r#type::{BareNativeTypeB, bare_native_type},
};

use super::SnapshotError;

/// Process-local native type objects indexed by snapshot-stable qualified names.
///
/// Native type constructors are cheap and independent of Ferlium source compilation, so this
/// catalog is built directly from Rust. A snapshot stores only these names and type arguments.
pub(crate) struct NativeTypeCatalog {
    by_name: BTreeMap<&'static str, BareNativeTypeB>,
}

impl NativeTypeCatalog {
    pub(crate) fn std() -> Self {
        let mut catalog = Self {
            by_name: BTreeMap::new(),
        };
        // Construct only bare native descriptors here. Calling the public `*_type()` helpers
        // would intern types merely by inspecting the catalog, perturbing compiler behavior before
        // std compilation and making cache results depend on interner insertion order.
        catalog.register("std::()", bare_native_type::<()>());
        catalog.register("std::bool", bare_native_type::<bool>());
        catalog.register("std::int", bare_native_type::<math::Int>());
        catalog.register("std::float", bare_native_type::<math::Float>());
        catalog.register("std::string", bare_native_type::<string::String>());
        catalog.register("std::hash", bare_native_type::<hash::HashValue>());
        catalog.register("std::hasher", bare_native_type::<hash::Hasher>());
        catalog.register(
            "std::unordered_hasher",
            bare_native_type::<hash::UnorderedHasher>(),
        );
        catalog.register(
            "std::string_iterator",
            bare_native_type::<string::StringIterator>(),
        );
        catalog.register(
            "std::string_split_iterator",
            bare_native_type::<string::StringSplitIterator>(),
        );
        catalog.register("std::Buffer", buffer_bare_native_type());
        catalog.register("std::StaticStr", bare_native_type::<string::StaticStr>());
        catalog
    }

    fn register(&mut self, canonical_name: &'static str, native: BareNativeTypeB) {
        assert!(
            self.by_name.insert(canonical_name, native).is_none(),
            "duplicate native type name {canonical_name}"
        );
    }

    pub(crate) fn resolve(&self, canonical_name: &str) -> Option<BareNativeTypeB> {
        self.by_name.get(canonical_name).cloned()
    }

    pub(crate) fn canonical_name(&self, native: &BareNativeTypeB) -> Option<String> {
        self.by_name
            .iter()
            .find_map(|(name, candidate)| (candidate == native).then(|| (*name).to_owned()))
    }

    pub(crate) fn canonical_names(&self) -> impl Iterator<Item = &'static str> + '_ {
        self.by_name.keys().copied()
    }

    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn require_name(&self, native: &BareNativeTypeB) -> Result<String, SnapshotError> {
        self.canonical_name(native)
            .ok_or_else(|| SnapshotError::UnnamedNativeType(native.type_name().to_owned()))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{CompilerSession, types::r#type::TypeKind};

    #[test]
    fn catalog_covers_std_native_aliases() {
        let session = CompilerSession::new();
        let module = session.std_module();
        let catalog = NativeTypeCatalog::std();

        for alias in module.type_aliases.type_entries() {
            if let TypeKind::Native(native) = &*alias.ty.data() {
                let name = catalog.require_name(&native.bare_ty).unwrap();
                assert_eq!(catalog.resolve(&name).unwrap(), native.bare_ty);
            }
        }
        for (_, native) in module.type_aliases.bare_native_iter() {
            let name = catalog.require_name(native).unwrap();
            assert_eq!(catalog.resolve(&name).unwrap(), *native);
        }
    }
}
