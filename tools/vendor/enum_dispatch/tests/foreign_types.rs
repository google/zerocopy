use core::convert::TryInto;
use enum_dispatch::enum_dispatch;

#[enum_dispatch]
trait IsAttribute {
    fn size(&self) -> usize;
}

impl IsAttribute for Vec<f32> {
    fn size(&self) -> usize {
        self.len() * std::mem::size_of::<f32>()
    }
}
impl IsAttribute for Vec<f64> {
    fn size(&self) -> usize {
        self.len() * std::mem::size_of::<f64>()
    }
}

#[enum_dispatch(IsAttribute)]
enum AnyAttribute {
    VariantVector2Forf32(Vec<f32>),
    VariantVector3Forf32(Vec<f64>),
}

#[test]
fn main() {
    let floats: Vec<f32> = vec![0., 1., 2., 3.];
    let doubles: Vec<f64> = vec![0., 1., 2., 3., 4., 5., 6., 7.];

    let mut all: Vec<AnyAttribute> = vec![floats.into(), doubles.into()];

    assert_eq!(all[0].size(), 16);
    assert_eq!(all[1].size(), 64);

    let doubles: Vec<f64> = all.pop().unwrap().try_into().unwrap();
    let floats: Vec<f32> = all.pop().unwrap().try_into().unwrap();

    assert_eq!(floats, vec![0.0f32, 1., 2., 3.]);
    assert_eq!(doubles, vec![0.0f64, 1., 2., 3., 4., 5., 6., 7.]);
}
