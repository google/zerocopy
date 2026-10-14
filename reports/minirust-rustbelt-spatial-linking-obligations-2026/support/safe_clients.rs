// All executed code is safe Rust. No intentionally invalid Rust is executed.
use std::cell::Cell;

fn parser(bytes: &[u8]) -> Option<u16> {
    if bytes.len() < 2 { None } else { Some(u16::from_le_bytes([bytes[0], bytes[1]])) }
}
fn callback_read(cell: &Cell<u8>, callback: impl FnOnce()) -> (u8,u8) {
    let before=cell.get();
    callback();
    (before,cell.get())
}
fn main() {
    let mut parser_cases=0;
    for a in 0..=255u8 { for b in 0..=255u8 {
        let actual=parser(&[a,b]);
        let expected=Some(u16::from(a)+256*u16::from(b));
        if actual != expected { eprintln!("parser mismatch"); std::process::exit(1); }
        parser_cases+=1;
    }}
    let mut split_cases=0;
    for n in 0..=16usize { for mid in 0..=n {
        let mut values=vec![0u8;n];
        {
            let (left,right)=values.split_at_mut(mid);
            for x in left {*x=1;}
            for x in right {*x=2;}
        }
        if values[..mid].iter().any(|x|*x!=1) || values[mid..].iter().any(|x|*x!=2) {
            eprintln!("split mismatch");std::process::exit(1);
        }
        split_cases+=1;
    }}
    let mut callback_cases=0;
    let mut stale_read_counterexamples=0;
    for before in 0..=255u8 { for after in 0..=255u8 {
        let cell=Cell::new(before);
        let (x,y)=callback_read(&cell,||cell.set(after));
        if x!=before || y!=after {eprintln!("callback mismatch");std::process::exit(1);}
        if x!=y {stale_read_counterexamples+=1;}
        callback_cases+=1;
    }}
    println!("{{\"status\":\"pass\",\"parser_cases\":{parser_cases},\"split_cases\":{split_cases},\"callback_cases\":{callback_cases},\"stale_read_counterexamples\":{stale_read_counterexamples}}}");
}

