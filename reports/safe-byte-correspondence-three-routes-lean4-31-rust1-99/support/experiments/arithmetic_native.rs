#[path="instrumented.rs"] mod captured;
fn main() {
 for n in 0u16..256 {
  let x=n as u8;
  let (a,b,out)=captured::subject_trace(x);
  assert_eq!(captured::subject(x),out);
  println!("{},{},{},{}",n,a,b,out);
 }
}
