mod probe;
fn main() {
 let mut choose_count=0u64; let mut update_count=0u64;let mut digest=0u64;
 for b in [false,true] {for x in 0..=u8::MAX {for y in 0..=u8::MAX {
  let actual=probe::choose(std::hint::black_box(b),std::hint::black_box(x),std::hint::black_box(y));assert_eq!(actual,if b {x}else{y});
  choose_count+=1;digest=digest.wrapping_add(actual as u64);
 }}}
 for first in 0..=u8::MAX {for second in 0..=u8::MAX {for x in 0..=u8::MAX {
  let mut pair=(first,second);let frame=(99u8,23u8);
  probe::update_second(std::hint::black_box(&mut pair),std::hint::black_box(x));assert_eq!(pair,(first,x));assert_eq!(frame,(99,23));
  update_count+=1;digest=digest.wrapping_add(pair.0 as u64 * 257+pair.1 as u64);
 }}}
 println!("choose_cases={} update_cases={} digest={}",choose_count,update_count,digest);
}
