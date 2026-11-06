#[inline(always)] fn callee(x:u8)->u8 {if x==0 {panic!("intentional callee failure")}x.wrapping_add(1)}
#[inline(never)] fn caller(x:u8)->u8 {let _=callee(x);7}
fn main(){std::panic::set_hook(Box::new(|_|{}));let mut rejected=0;for x in 0..=255u8 {match std::panic::catch_unwind(||caller(x)){Ok(v)=>{assert_ne!(x,0);assert_eq!(v,7);},Err(_)=>{assert_eq!(x,0);rejected+=1;}}}assert_eq!(rejected,1);println!("inputs=256;callee_failure_preserved=1;successful_result=7;all_match=true");}
