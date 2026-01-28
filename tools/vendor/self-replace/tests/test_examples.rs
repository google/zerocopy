use std::env::consts::EXE_EXTENSION;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::{env, fs};

fn compile_example(name: &str) {
    let mut cmd = Command::new("cargo");
    let output = cmd
        .arg("build")
        .arg("--example")
        .arg(name)
        .output()
        .unwrap();
    println!("stdout:\n{}", String::from_utf8_lossy(&output.stdout));
    println!("stderr:\n{}", String::from_utf8_lossy(&output.stderr));
    assert!(output.status.success());
}

fn get_executable(name: &str, tempdir: &Path) -> PathBuf {
    let exe = env::current_exe()
        .unwrap()
        .parent()
        .unwrap()
        .parent()
        .unwrap()
        .join("examples")
        .join(name)
        .with_extension(EXE_EXTENSION);
    let final_exe = tempdir.join(exe.file_name().unwrap());
    fs::copy(&exe, &final_exe).unwrap();
    final_exe
}

struct RunOptions<'a> {
    path: &'a Path,
    force_exit: bool,
    scratchspace: &'a Path,
    expected_output: &'a str,
}

fn run(opts: RunOptions) {
    let mut cmd = Command::new(opts.path);
    if opts.force_exit {
        cmd.env("FORCE_EXIT", "1");
    }

    // env::temp_dir is used on windows to place temporaries in some
    // cases.  Put it onto our scratchspace so we can assert that it's
    // left empty behind.
    #[cfg(windows)]
    {
        cmd.env("TMP", opts.scratchspace);
        cmd.env("TEMP", opts.scratchspace);
    }

    // does not actually matter today, but maybe it once will
    #[cfg(unix)]
    {
        cmd.env("TMPDIR", opts.scratchspace);
    }

    let output = cmd.output().unwrap();
    assert!(output.status.success());
    #[cfg(windows)]
    {
        // takes a bit
        use std::time::Duration;
        std::thread::sleep(Duration::from_millis(200));
    }
    let stdout = std::str::from_utf8(&output.stdout).unwrap();
    assert_eq!(stdout.trim(), opts.expected_output);
}

#[test]
fn test_self_delete() {
    let workspace = tempfile::tempdir().unwrap();
    let scratchspace = tempfile::tempdir().unwrap();
    compile_example("deletes-itself");
    let exe = get_executable("deletes-itself", workspace.path());
    assert!(exe.is_file());
    run(RunOptions {
        path: &exe,
        force_exit: false,
        scratchspace: scratchspace.path(),
        expected_output: "When I finish, I am deleted",
    });
    assert!(!exe.is_file());
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[test]
fn test_self_delete_force_exit() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = tempfile::tempdir().unwrap();
    compile_example("deletes-itself");
    let exe = get_executable("deletes-itself", workspace.path());
    assert!(exe.is_file());
    run(RunOptions {
        path: &exe,
        force_exit: true,
        scratchspace: scratchspace.path(),
        expected_output: "When I finish, I am deleted",
    });
    assert!(!exe.is_file());
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[test]
fn test_self_delete_outside_path() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = tempfile::tempdir().unwrap();
    compile_example("deletes-itself-outside-path");
    let exe = get_executable("deletes-itself-outside-path", workspace.path());
    assert!(exe.is_file());
    assert!(workspace.path().is_dir());
    run(RunOptions {
        path: &exe,
        force_exit: false,
        scratchspace: scratchspace.path(),
        expected_output: "When I finish, all of my parent folder is gone.",
    });
    assert!(!exe.is_file());
    assert!(!workspace.path().is_dir());
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[test]
fn test_self_delete_outside_path_force_exit() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = tempfile::tempdir().unwrap();
    compile_example("deletes-itself-outside-path");
    let exe = get_executable("deletes-itself-outside-path", workspace.path());
    assert!(exe.is_file());
    assert!(workspace.path().is_dir());
    run(RunOptions {
        path: &exe,
        force_exit: true,
        scratchspace: scratchspace.path(),
        expected_output: "When I finish, all of my parent folder is gone.",
    });
    assert!(!exe.is_file());
    assert!(!workspace.path().is_dir());
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[test]
fn test_self_replace() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = scratchspace.path().join("workspace");
    fs::create_dir_all(&workspace).unwrap();

    compile_example("replaces-itself");
    compile_example("hello");

    let exe = get_executable("replaces-itself", &workspace);
    let hello = get_executable("hello", &workspace);

    assert!(exe.is_file());
    assert!(hello.is_file());

    run(RunOptions {
        path: &exe,
        force_exit: true,
        scratchspace: scratchspace.path(),
        expected_output: "Next time I run, I am the hello executable",
    });
    assert!(exe.is_file());
    assert!(hello.is_file());
    run(RunOptions {
        path: &exe,
        force_exit: false,
        scratchspace: scratchspace.path(),
        expected_output: "Hello World!",
    });

    fs::remove_dir_all(&workspace).unwrap();
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[test]
fn test_self_replace_force_exit() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = scratchspace.path().join("workspace");
    fs::create_dir_all(&workspace).unwrap();

    compile_example("replaces-itself");
    compile_example("hello");

    let exe = get_executable("replaces-itself", &workspace);
    let hello = get_executable("hello", &workspace);

    assert!(exe.is_file());
    assert!(hello.is_file());

    run(RunOptions {
        path: &exe,
        force_exit: true,
        scratchspace: scratchspace.path(),
        expected_output: "Next time I run, I am the hello executable",
    });
    assert!(exe.is_file());
    assert!(hello.is_file());
    run(RunOptions {
        path: &exe,
        force_exit: false,
        scratchspace: scratchspace.path(),
        expected_output: "Hello World!",
    });

    fs::remove_dir_all(&workspace).unwrap();
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}

#[cfg(unix)]
#[test]
fn test_self_replace_through_symlink() {
    let scratchspace = tempfile::tempdir().unwrap();
    let workspace = scratchspace.path().join("workspace");
    fs::create_dir_all(&workspace).unwrap();

    compile_example("replaces-itself");
    compile_example("hello");

    let exe = get_executable("replaces-itself", &workspace);
    let hello = get_executable("hello", &workspace);

    let exe_symlink = workspace.join("bin").join("symlink");
    fs::create_dir_all(exe_symlink.parent().unwrap()).unwrap();
    std::os::unix::fs::symlink(&exe, &exe_symlink).unwrap();

    assert!(exe.is_file());
    assert!(hello.is_file());
    assert!(std::fs::symlink_metadata(&exe_symlink)
        .unwrap()
        .file_type()
        .is_symlink());

    run(RunOptions {
        path: &exe_symlink,
        force_exit: true,
        scratchspace: scratchspace.path(),
        expected_output: "Next time I run, I am the hello executable",
    });
    assert!(exe.is_file());
    assert!(hello.is_file());
    assert!(std::fs::symlink_metadata(&exe_symlink)
        .unwrap()
        .file_type()
        .is_symlink());
    run(RunOptions {
        path: &exe_symlink,
        force_exit: false,
        scratchspace: scratchspace.path(),
        expected_output: "Hello World!",
    });

    fs::remove_dir_all(&workspace).unwrap();
    assert!(scratchspace.path().read_dir().unwrap().next().is_none());
}
