mod subject {include!("lib.rs");}
fn main(){let start=std::time::Instant::now();let mut cases=0;
for seed in 0..32 {for len in 0..=64 {for dest in [0,1,2,16,63,64,128] {for mode in 0..4 {assert_eq!(subject::check_case(seed,len,dest,mode),0);cases+=1;}}}}
for byte in 0..256 {for index in 0..4 {assert_eq!(subject::invalid_flag(byte,index),0);}}
assert_eq!(subject::check_case(0,65,0,0),99);assert_eq!(subject::invalid_flag(256,0),99);
println!("cases={cases};flag_controls=1024;out_of_domain=2;all_match=true");
println!("layout={:?}",(0..5).map(subject::layout).collect::<Vec<_>>());println!("runtime_ns={}",start.elapsed().as_nanos());}
