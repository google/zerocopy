use async_scoped::{
    spawner::{Blocker, Spawner},
    Scope,
};
use futures::future::pending;
use std::hint::black_box;

fn spawn_and_collect<Sp: Spawner<usize> + Blocker>(s: &mut Scope<usize, Sp>) {
    const INPUT_SIZE: usize = 1000000;
    const MAX_DELAY: usize = 1 << 8;
    for i in 0..INPUT_SIZE {
        let delay = i & MAX_DELAY;
        s.spawn(async move {
            let _ = async_std::future::timeout(
                std::time::Duration::from_millis((MAX_DELAY - delay) as u64),
                pending::<()>(),
            )
            .await;
            i
        });
    }
}

fn main() {
    let r = {
        #[cfg(feature = "async-std")]
        {
            // Async-std runtime does not have a straightforward way to configure multi-threaded
            // runtime: https://docs.rs/async-std/latest/async_std/index.html#runtime-configuration
            // ASYNC_STD_THREAD_COUNT environment variable must be used to match the Tokio benchmark
            use async_scoped::AsyncStdScope;
            let (_, r) = AsyncStdScope::scope_and_block(spawn_and_collect);

            r
        }
        #[cfg(feature = "use-tokio")]
        {
            use async_scoped::TokioScope;
            tokio::runtime::Builder::new_multi_thread()
                .worker_threads(4)
                .build()
                .unwrap()
                .block_on(async move {
                    let (_, r) = TokioScope::scope_and_block(spawn_and_collect);

                    r
                })
        }
    };

    r.into_iter().for_each(|v| {
        let _ = black_box(v);
    })
}
