use crate::spawner::*;
use crate::Scope;

impl<'a, T, Sp: Spawner<T> + Blocker + Default> Scope<'a, T, Sp> {
    /// Creates a `Scope` to spawn non-'static futures. The
    /// function is called with a block which takes an `&mut
    /// Scope`. The `spawn` method on this arg. can be used to
    /// spawn "local" futures.
    ///
    /// # Returns
    ///
    /// The function returns the created `Scope`, and the return
    /// value of the block passed to it. The returned stream and
    /// is expected to be driven completely before being
    /// forgotten. Dropping this stream causes the stream to be
    /// driven _while blocking the current thread_. The values
    /// returned from the stream are the output of the futures
    /// spawned.
    ///
    /// # Safety
    ///
    /// The returned stream is expected to be run to completion
    /// before being forgotten. Dropping it is okay, but blocks
    /// the current thread until all spawned futures complete.
    pub unsafe fn scope<R, F>(f: F) -> (Self, R)
    where
        T: Send + 'static,
        Sp: Spawner<T> + Blocker,
        F: FnOnce(&mut Scope<'a, T, Sp>) -> R,
    {
        let mut scope = Scope::create(Default::default());
        let op = f(&mut scope);
        (scope, op)
    }

    /// A function that creates a scope and immediately awaits,
    /// _blocking the current thread_ for spawned futures to
    /// complete. The outputs of the futures are collected as a
    /// `Vec` and returned along with the output of the block.
    ///
    /// # Safety
    ///
    /// This function is safe to the best of our understanding
    /// as it blocks the current thread until the stream is
    /// driven to completion, implying that all the spawned
    /// futures have completed too. However, care must be taken
    /// to ensure a recursive usage of this function doesn't
    /// lead to deadlocks.
    ///
    /// When scope is used recursively, you may also use the
    /// unsafe `scope_and_*` functions as long as this function
    /// is used at the top level. In this case, either the
    /// recursively spawned should have the same lifetime as the
    /// top-level scope, or there should not be any spurious
    /// future cancellations within the top level scope.
    pub fn scope_and_block<R, F>(f: F) -> (R, Vec<Sp::FutureOutput>)
    where
        T: Send + 'static,
        Sp: Spawner<T> + Blocker,
        F: FnOnce(&mut Scope<'a, T, Sp>) -> R,
    {
        let (mut stream, block_output) = unsafe { Self::scope(f) };
        let proc_outputs = Sp::default().block_on(stream.collect());
        (block_output, proc_outputs)
    }

    /// An asynchronous function that creates a scope and
    /// immediately awaits the stream. The outputs of the
    /// futures are collected as a `Vec` and returned along with
    /// the output of the block.
    ///
    /// # Safety
    ///
    /// This function is _not completely safe_: please see
    /// `cancellation_soundness` in [tests.rs][tests-src] for a
    /// test-case that suggests how this can lead to invalid
    /// memory access if not dealt with care.
    ///
    /// The caller must ensure that the lifetime 'a is valid
    /// until the returned future is fully driven. Dropping the
    /// future is okay, but blocks the current thread until all
    /// spawned futures complete.
    ///
    /// [tests-src]: https://github.com/rmanoka/async-scoped/blob/master/src/tests.rs
    pub async unsafe fn scope_and_collect<R, F>(f: F) -> (R, Vec<Sp::FutureOutput>)
    where
        T: Send + 'static,
        F: FnOnce(&mut Scope<'a, T, Sp>) -> R,
    {
        let (mut stream, block_output) = Self::scope(f);
        let proc_outputs = stream.collect().await;
        (block_output, proc_outputs)
    }
}
