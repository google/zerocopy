use std::arch::global_asm;
use std::sync::{Arc, Barrier};
use std::sync::atomic::{AtomicU32, AtomicU64, Ordering};
use std::thread;

global_asm!(r#"
.text
.p2align 2
.globl _anneal_publish_relaxed
_anneal_publish_relaxed:
 mov w8, #1
 str w8, [x0]
 str w8, [x1]
 ret
.globl _anneal_publish_release
_anneal_publish_release:
 mov w8, #1
 str w8, [x0]
 stlr w8, [x1]
 ret
.globl _anneal_observe_relaxed
_anneal_observe_relaxed:
 ldr w8, [x1]
 ldr w9, [x0]
 orr x0, x9, x8, lsl #32
 ret
.globl _anneal_observe_acquire
_anneal_observe_acquire:
 ldapr w8, [x1]
 ldr w9, [x0]
 orr x0, x9, x8, lsl #32
 ret
.globl _anneal_sb_relaxed
_anneal_sb_relaxed:
 mov w8, #1
 str w8, [x0]
 ldr w0, [x1]
 ret
.globl _anneal_sb_ra
_anneal_sb_ra:
 mov w8, #1
 stlr w8, [x0]
 ldapr w0, [x1]
 ret
.globl _anneal_sb_sc
_anneal_sb_sc:
 mov w8, #1
 stlr w8, [x0]
 ldar w0, [x1]
 ret
.globl _anneal_sb_fence
_anneal_sb_fence:
 mov w8, #1
 str w8, [x0]
 dmb ish
 ldr w0, [x1]
 ret
"#);
unsafe extern "C" {
 fn anneal_publish_relaxed(data: *mut u32, flag: *mut u32);
 fn anneal_publish_release(data: *mut u32, flag: *mut u32);
 fn anneal_observe_relaxed(data: *mut u32, flag: *mut u32) -> u64;
 fn anneal_observe_acquire(data: *mut u32, flag: *mut u32) -> u64;
 fn anneal_sb_relaxed(own: *mut u32, peer: *mut u32) -> u32;
 fn anneal_sb_ra(own: *mut u32, peer: *mut u32) -> u32;
 fn anneal_sb_sc(own: *mut u32, peer: *mut u32) -> u32;
 fn anneal_sb_fence(own: *mut u32, peer: *mut u32) -> u32;
}
#[repr(align(128))]
struct Line(AtomicU32);
struct Shared { x: Line, y: Line, a: AtomicU64, b: AtomicU64, start: Barrier, done: Barrier }
#[derive(Clone, Copy)]
enum Mode { MpRelaxed, MpReleaseAcquire, SbRelaxed, SbRa, SbSc, SbFence }
fn run(mode: Mode, rounds: usize) -> Result<[usize;4], String> {
 let s = Arc::new(Shared { x: Line(AtomicU32::new(0)), y: Line(AtomicU32::new(0)), a: AtomicU64::new(0), b: AtomicU64::new(0), start: Barrier::new(3), done: Barrier::new(3) });
 let first = s.clone();
 let t0 = thread::spawn(move || { for _ in 0..rounds {
  first.start.wait(); let x=first.x.0.as_ptr(); let y=first.y.0.as_ptr();
  let a = unsafe { match mode {
   Mode::MpRelaxed => { anneal_publish_relaxed(x,y); 0 },
   Mode::MpReleaseAcquire => { anneal_publish_release(x,y); 0 },
   Mode::SbRelaxed => anneal_sb_relaxed(x,y), Mode::SbRa => anneal_sb_ra(x,y),
   Mode::SbSc => anneal_sb_sc(x,y), Mode::SbFence => anneal_sb_fence(x,y)
  }}; first.a.store(a as u64,Ordering::Relaxed); first.done.wait();
 }});
 let second=s.clone();
 let t1=thread::spawn(move || { for _ in 0..rounds {
  second.start.wait(); let x=second.x.0.as_ptr(); let y=second.y.0.as_ptr();
  let b = unsafe { match mode {
   Mode::MpRelaxed => anneal_observe_relaxed(x,y),
   Mode::MpReleaseAcquire => anneal_observe_acquire(x,y),
   Mode::SbRelaxed => anneal_sb_relaxed(y,x) as u64, Mode::SbRa => anneal_sb_ra(y,x) as u64,
   Mode::SbSc => anneal_sb_sc(y,x) as u64, Mode::SbFence => anneal_sb_fence(y,x) as u64
  }}; second.b.store(b,Ordering::Relaxed); second.done.wait();
 }});
 let mut counts=[0;4]; let mut bad=None;
 for _ in 0..rounds {
  s.x.0.store(0,Ordering::Relaxed);s.y.0.store(0,Ordering::Relaxed);s.start.wait();s.done.wait();
  let a=s.a.load(Ordering::Relaxed);let b=s.b.load(Ordering::Relaxed);
  let (one,two)=if matches!(mode,Mode::MpRelaxed|Mode::MpReleaseAcquire) {(b>>32,b&0xffffffff)}else{(a,b)};
  if one>1||two>1 {bad=Some(format!("out-of-domain result {one},{two}"));}else{counts[(one*2+two)as usize]+=1;}
 }
 if t0.join().is_err()||t1.join().is_err(){return Err("thread failure".into());}
 if let Some(e)=bad{return Err(e);}
 if matches!(mode,Mode::MpReleaseAcquire)&&counts[2]!=0{return Err("model-forbidden MP observation".into());}
 if matches!(mode,Mode::SbSc|Mode::SbFence)&&counts[0]!=0{return Err("model-forbidden SB observation".into());}
 Ok(counts)
}
fn main()->std::process::ExitCode {
 if !std::arch::is_aarch64_feature_detected!("rcpc") {println!("unsupported: RCpc absent");return std::process::ExitCode::from(2);}
 for(name,mode)in[("MP-relaxed",Mode::MpRelaxed),("MP-release-acquire",Mode::MpReleaseAcquire),("SB-relaxed",Mode::SbRelaxed),("SB-release-acquire",Mode::SbRa),("SB-seqcst",Mode::SbSc),("SB-fence",Mode::SbFence)] {
  match run(mode,10000) {Ok(c)=>println!("{name}: rounds=10000 counts00_01_10_11={c:?}"),Err(e)=>{eprintln!("{name}: {e}");return std::process::ExitCode::from(1);}}
 }
 std::process::ExitCode::SUCCESS
}
