use std::{cell::{Cell,RefCell},rc::Rc};
use std::panic::{catch_unwind,AssertUnwindSafe};
type Log=Rc<RefCell<Vec<&'static str>>>;
struct Token(&'static str,Log);
impl Drop for Token {fn drop(&mut self){self.1.borrow_mut().push(self.0);}}
struct Bomb(Log);
impl Drop for Bomb {fn drop(&mut self){self.0.borrow_mut().push("bomb");panic!("expected destructor unwind");}}
struct Select;
trait Pick{fn pick(self)->u8;}
impl Pick for Select{fn pick(self)->u8{1}}
impl Pick for &Select{fn pick(self)->u8{2}}
fn with_fields<'a>(p:&'a mut (u8,Cell<u8>),cb:impl FnOnce(&Cell<u8>))->&'a mut u8{
 cb(&p.1); &mut p.0
}
fn main(){
 // Both panics are deliberately caught; any other panic is unexpected.
 std::panic::set_hook(Box::new(|_|{}));
 let l:Log=Default::default();
 let partial=catch_unwind(AssertUnwindSafe({
  let l=l.clone();
  move ||{let _outer=Token("outer",l.clone());
    let pair=(Token("left",l.clone()),Token("right",l.clone()));
    let moved=pair.0;drop(moved);panic!("expected body unwind");}
 }));
 println!("partial_caught={};drops={:?}",partial.is_err(),*l.borrow());
 l.borrow_mut().clear();
 let destructor=catch_unwind(AssertUnwindSafe({
  let l=l.clone();
  move || {let _outer=Token("outer",l.clone());let _bomb=Bomb(l.clone());
    l.borrow_mut().push("body");}
 }));
 println!("destructor_caught={};drops={:?}",destructor.is_err(),*l.borrow());
 l.borrow_mut().clear();
 {let _=Token("wildcard",l.clone());l.borrow_mut().push("after_wildcard");
  let _bound=Token("binding",l.clone());l.borrow_mut().push("after_binding");}
 println!("binding_drop_order={:?}",*l.borrow());
 let mut pair=(3,Cell::new(4));
 *with_fields(&mut pair,|c|c.set(9))=7;
 println!("callback_fields={},{}",pair.0,pair.1.get());
 println!("selected_impls={},{}",Select.pick(),(&Select).pick());
}

