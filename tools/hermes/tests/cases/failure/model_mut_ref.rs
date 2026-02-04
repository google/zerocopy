// @ lean model model_mut_ref(x)
// @ requires true
// @ ensures true
#[allow(unused)]
unsafe fn model_mut_ref(x: &mut u32) {
    *x = 0;
}

fn main() {}
