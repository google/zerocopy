#[derive(Clone,Copy,Debug,PartialEq,Eq)]
struct Pair { left:u8, right:u8 }
fn update_field(p: &mut Pair, delta:u8) -> u8 {
 let left = &mut p.left;
 *left = (*left).wrapping_add(delta);
 p.right
}
fn update_slice(xs: &mut [u8], index:usize, delta:u8) -> Option<u8> {
 let slot = xs.get_mut(index)?;
 *slot = (*slot).wrapping_add(delta);
 Some(*slot)
}
fn mix(h:&mut u64,x:u8) { *h=(*h ^ (x as u64)).wrapping_mul(1099511628211); }
fn main() {
 let delta=3u8;
 let mut field_count=0u64;
 let mut slice_count=0u64;
 let mut digest=14695981039346656037u64;
 for a in 0u16..256 {
  for b in 0u16..256 {
   let original=Pair{left:a as u8,right:b as u8};
   let mut p=original;
   let returned=update_field(&mut p,delta);
   assert_eq!(p.left,((a+3)%256) as u8);
   assert_eq!(p.right,original.right);
   assert_eq!(returned,original.right);
   mix(&mut digest,p.left);mix(&mut digest,p.right);mix(&mut digest,returned);
   field_count+=1;
   for index in 0usize..3 {
    let before=[a as u8,b as u8];
    let mut xs=before;
    let out=update_slice(&mut xs,index,delta);
    if index<2 {
      let expected=((before[index] as u16+3)%256) as u8;
      assert_eq!(out,Some(expected));
      assert_eq!(xs[index],expected);
      assert_eq!(xs[1-index],before[1-index]);
    } else {
      assert_eq!(out,None);assert_eq!(xs,before);
    }
    mix(&mut digest,xs[0]);mix(&mut digest,xs[1]);
    mix(&mut digest,out.unwrap_or(0));
    slice_count+=1;
   }
  }
 }
 println!("field_cases={} slice_cases={} fixed_delta={} fnv64={:016x}",field_count,slice_count,delta,digest);
}

