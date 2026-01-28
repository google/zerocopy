use duct::cmd;
use std::env;
use std::io;
use std::thread;
use std::time::Duration;

fn run_child() -> io::Result<()> {
    // What the child does is start the grandchild (which is this same exe with
    // an extra flag), print "started" to indicate that that's done, and then
    // wait on the grandchild.
    let grandchild = cmd!(env::current_exe()?, "--grandchild").start()?;
    println!("started");
    grandchild.wait()?;
    Ok(())
}

fn run_grandchild() -> io::Result<()> {
    // All the grandchild does is sleep "forever". (Forever equals one day.)
    //
    // Ultimately the test is going to leak this sleeping process. That's kind
    // of the point of what it's testing, and it's hard to avoid without
    // creating some sort of race condition. Apologies to anyone who runs this
    // test thousands of times a day.
    thread::sleep(Duration::from_secs(24 * 60 * 60));
    Ok(())
}

fn main() -> io::Result<()> {
    let args: Vec<String> = env::args().collect();
    if args.len() > 1 {
        assert_eq!(args.len(), 2);
        assert_eq!(&args[1], "--grandchild");
        run_grandchild()
    } else {
        run_child()
    }
}
