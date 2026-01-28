#![feature(async_fn_in_trait)]

use enum_dispatch::enum_dispatch;

struct A;
struct B;

impl XTrait for A {
    async fn run(&mut self) -> Result<u32, ()> {
        Ok(10)
    }
}
impl XTrait for B {
    async fn run(&mut self) -> Result<u32, ()> {
        Ok(20)
    }
}

#[enum_dispatch]
enum X {
    A,
    B,
}

#[enum_dispatch(X)]
trait XTrait {
    async fn run(&mut self) -> Result<u32, ()>;
}

fn main() -> smol::io::Result<()> {
    let mut a: X = A.into();
    let mut b: X = B.into();

    smol::block_on(async {
        assert_eq!(10, a.run().await.unwrap());
        assert_eq!(20, b.run().await.unwrap());
        Ok(())
    })
}
