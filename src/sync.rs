/// Helper phantom data to make NativeType Sync
#[derive(Clone, Copy)]
pub(crate) struct SyncPhantomData<T: ?Sized> {
    phantom: std::marker::PhantomData<std::sync::atomic::AtomicPtr<Box<T>>>,
}
impl<T: ?Sized> Default for SyncPhantomData<T> {
    fn default() -> Self {
        Self {
            phantom: std::marker::PhantomData,
        }
    }
}
