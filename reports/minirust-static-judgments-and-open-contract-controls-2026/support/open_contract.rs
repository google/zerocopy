use std::cell::Cell;
use std::cell::RefCell;
use std::ops::Deref;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::future::Future;
use std::pin::Pin;
use std::sync::Arc;
use std::task::{Context, Poll, Wake, Waker};

trait Family { type View<'a>: AsRef<[u8]> where Self:'a; fn view(&self)->Self::View<'_>; }
struct Store<const N:usize>([u8;N]);
impl<const N:usize> Family for Store<N> {
    type View<'a> = &'a [u8] where Self:'a;
    fn view(&self)->Self::View<'_> { &self.0 }
}
trait Value { fn value()->u32; }
struct A; struct B;
impl Value for A { fn value()->u32 { 10 } }
impl Value for B { fn value()->u32 { 20 } }
fn instance<T:Value,const N:u32>()->u32 { T::value()+N }
struct Wrapper([u8;2]);
impl Deref for Wrapper { type Target=[u8]; fn deref(&self)->&[u8] {&self.0} }
#[cfg(feature_flip)]
impl Wrapper { fn len(&self)->usize {99} }
macro_rules! generated {($name:ident,$value:expr)=>{fn $name()->usize {$value}};}
generated!(generated_count, std::mem::size_of::<usize>());

struct Stamp<'a>(&'a RefCell<Vec<u8>>,u8);
impl Stamp<'_> {fn id(&self)->u8 {self.1}}
impl Drop for Stamp<'_> {fn drop(&mut self){self.0.borrow_mut().push(self.1)}}

struct Busy<'a>(&'a Cell<bool>);
impl Drop for Busy<'_> {fn drop(&mut self){self.0.set(false)}}
fn acquire(flag:&Cell<bool>)->Option<Busy<'_>> {
    if flag.replace(true) {None} else {Some(Busy(flag))}
}
fn relay1(s:&mut[u8])->&mut[u8] { &mut s[1..] }
fn relay2(s:&mut[u8])->&mut[u8] { relay1(relay1(s)) }
fn callback_and_return(s:&mut[u8],callback:impl FnOnce(&mut[u8]))->&mut[u8] {
    let (left,right)=s.split_at_mut(2); callback(left); right
}
struct Noop; impl Wake for Noop {fn wake(self:Arc<Self>) {}}
struct TwoPoll {state:u8,drops:Arc<CellLike>}
// A mutex supplies Send + Sync for the safe std::task::Wake boundary.
struct CellLike(std::sync::Mutex<u32>);
impl Drop for TwoPoll {fn drop(&mut self){*self.drops.0.lock().unwrap()+=1}}
impl Future for TwoPoll {
    type Output=u8;
    fn poll(self:Pin<&mut Self>,_:&mut Context<'_>)->Poll<u8> {
        let me=self.get_mut(); me.state+=1;
        if me.state==1 {Poll::Pending} else {Poll::Ready(7)}
    }
}
fn main() {
    let store=Store([1u8,2,3]);
    println!("family={}",store.view().as_ref().len());
    println!("instances={},{}",instance::<A,1>(),instance::<B,1>());
    println!("resolved_len={}",Wrapper([1,2]).len());
    println!("macro_word={}",generated_count());
    let temporary_log=RefCell::new(Vec::new());
    {let _extended=&Stamp(&temporary_log,1);temporary_log.borrow_mut().push(10);}
    {let _value=(&Stamp(&temporary_log,2)).id();temporary_log.borrow_mut().push(20);}
    println!("temporary_drops={:?}",temporary_log.borrow());
    let pattern_log=RefCell::new(Vec::new());
    match Some(Stamp(&pattern_log,3)) {Some(_)=>pattern_log.borrow_mut().push(30),None=>()}
    pattern_log.borrow_mut().push(40);
    match Some(Stamp(&pattern_log,4)) {Some(value)=>{drop(value);pattern_log.borrow_mut().push(50)},None=>()}
    pattern_log.borrow_mut().push(60);
    println!("pattern_drops={:?}",pattern_log.borrow());
    let retained=Cell::new(0u32); let busy=Cell::new(false);
    let mut bytes=[0u8,1,2,3,4,5];
    let returned=callback_and_return(&mut bytes,|left| {
        let _guard=acquire(&busy).unwrap();
        assert!(acquire(&busy).is_none());
        retained.set(retained.get()+1); left[0]=9;
    });
    relay2(returned)[0]=8;
    assert!(!busy.get());
    println!("callback_retained={},bytes={:?}",retained.get(),bytes);
    // Expected, caught panic; the default hook is intentionally preserved in stderr.
    let result=catch_unwind(AssertUnwindSafe(|| {
        let _guard=acquire(&busy).unwrap();
        retained.set(retained.get()+1);
        panic!("owned expected callback panic");
    }));
    assert!(result.is_err() && !busy.get());
    println!("panic_restored={},retained={}",!busy.get(),retained.get());
    let mut v=vec![1u8,2,3];
    let capacity_error=v.try_reserve(usize::MAX).is_err();
    assert_eq!(v,[1,2,3]); println!("capacity_overflow_preserves={}",capacity_error);
    let drops=Arc::new(CellLike(std::sync::Mutex::new(0)));
    let waker=Waker::from(Arc::new(Noop)); let mut cx=Context::from_waker(&waker);
    let mut future=Box::pin(TwoPoll{state:0,drops:drops.clone()});
    assert!(future.as_mut().poll(&mut cx).is_pending()); drop(future);
    assert_eq!(*drops.0.lock().unwrap(),1);
    println!("pending_future_drops={}",*drops.0.lock().unwrap());
}
