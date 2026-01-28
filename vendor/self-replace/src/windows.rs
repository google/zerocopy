use std::env;
use std::fs;
use std::io;
use std::mem;
use std::os::windows::prelude::OsStrExt;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::ptr;
use std::thread;
use std::time::Duration;

use windows_sys::Win32::Foundation::{
    CloseHandle, DuplicateHandle, LocalFree, DUPLICATE_SAME_ACCESS, GENERIC_READ, HANDLE,
    INVALID_HANDLE_VALUE, MAX_PATH, WAIT_OBJECT_0,
};
use windows_sys::Win32::Security::SECURITY_ATTRIBUTES;
use windows_sys::Win32::Storage::FileSystem::{
    CreateFileW, DeleteFileW, FILE_FLAG_DELETE_ON_CLOSE, FILE_SHARE_DELETE, FILE_SHARE_READ,
    OPEN_EXISTING,
};
use windows_sys::Win32::System::Environment::GetCommandLineW;
use windows_sys::Win32::System::LibraryLoader::GetModuleFileNameW;
use windows_sys::Win32::System::Threading::{
    CreateProcessA, ExitProcess, GetCurrentProcess, WaitForSingleObject, CREATE_NO_WINDOW,
    INFINITE, PROCESS_INFORMATION, STARTUPINFOA,
};
use windows_sys::Win32::UI::Shell::CommandLineToArgvW;

static SELFDELETE_SUFFIX: &str = ".__selfdelete__.exe";
static RELOCATED_SUFFIX: &str = ".__relocated__.exe";
static TEMP_SUFFIX: &str = ".__temp__.exe";

extern "C" {
    fn _wtoi64(x: *const u16) -> i64;
}

macro_rules! cstrdup {
    ($target:ident, $s:expr) => {
        let mut $target = [0u8; $s.len()];
        $target.copy_from_slice($s);
    };
}

/// Spawn a the temporary exe an instruct it to delete the original exe.
/// The child will then wait until we are shut down so this temporary exe
/// hangs around until we shut down.  We pass that exe the name of the original
/// file as well as a duplicate of the current process' handles.
fn spawn_tmp_exe_to_delete_parent(
    tmp_exe: PathBuf,
    original_exe: PathBuf,
) -> Result<(), io::Error> {
    let tmp_exe_win: Vec<_> = tmp_exe.as_os_str().encode_wide().chain(Some(0)).collect();
    let sa = SECURITY_ATTRIBUTES {
        nLength: mem::size_of::<SECURITY_ATTRIBUTES>() as u32,
        lpSecurityDescriptor: ptr::null_mut(),
        bInheritHandle: 1,
    };

    let tmp_handle = unsafe {
        CreateFileW(
            tmp_exe_win.as_ptr(),
            GENERIC_READ,
            FILE_SHARE_READ | FILE_SHARE_DELETE,
            &sa,
            OPEN_EXISTING,
            FILE_FLAG_DELETE_ON_CLOSE,
            0,
        )
    };
    if tmp_handle == INVALID_HANDLE_VALUE {
        return Err(io::Error::last_os_error());
    }

    // We need to upgrade the pseudo current process handle to the real one for the
    // temp executable.
    let mut process_handle = 0;
    unsafe {
        if DuplicateHandle(
            GetCurrentProcess(),
            GetCurrentProcess(),
            GetCurrentProcess(),
            &mut process_handle,
            0,
            1,
            DUPLICATE_SAME_ACCESS,
        ) == 0
        {
            CloseHandle(tmp_handle);
            return Err(io::Error::last_os_error());
        }
    };

    Command::new(tmp_exe)
        .arg(process_handle.to_string())
        .arg(original_exe)
        .spawn()?;

    // Many implementations of this sort of logic sleep here.  This one included.  However
    // it does not appear that the sleep here is actually necessary from my testing so I
    // would be happy to remvoe it.  The motivation here is that if we close our `tmp_handle`
    // too quickly, the process might nto have inherited it.
    thread::sleep(Duration::from_millis(100));

    unsafe {
        CloseHandle(process_handle);
        CloseHandle(tmp_handle);
    }
    Ok(())
}

/// This allows us to register a function that self destroys the process on startup
/// in certain circumstances.  We pick `.CRT$XCV` here because that section is
/// currently used after rust is initialized.
#[used]
#[link_section = ".CRT$XCV"]
static INIT_TABLE_ENTRY: unsafe extern "C" fn() = self_delete_on_init;

/// This function is called in "life before main" which is not allowed by Rust rules.
/// As such this function really should not do any funk rust business, and we instead
/// only use winapi functions directly here.  The exception to this rule is that we
/// actually use a slice iterator and `mem::zeroed` which is most likely fine given
/// that these functions won't allocate anything.
///
/// The logic of this is heavily inspired by the implementation of rustup which itself
/// is modelled after a blog post that no longer exists.  However a copy pasted version
/// of it can be found here: https://0x00sec.org/t/self-deleting-executables/33702
unsafe extern "C" fn self_delete_on_init() {
    // Check if our executable ends with SELFDELETE_SUFFIX.  If it does, we enter
    // deletion mode.  If it does not, this function does nothing and we continue
    // with regular execution.  Note that we intentionally do not try to support
    // executable names longer than MAX_PATH here.  This is done because in practice
    // you would run into much bigger issues for executables with a path that long.
    // In case anyone ever runs into it, a fix can be considered.  However fixing this
    // requires allocating an extra buffer on every startup and that seems pointless
    // for such an uncommon case.
    let mut exe_path = [0u16; MAX_PATH as _];
    let exe_path_len = GetModuleFileNameW(0, exe_path.as_mut_ptr(), MAX_PATH);
    if exe_path_len == 0
        || exe_path[..exe_path_len as _]
            .iter()
            .rev()
            .take(SELFDELETE_SUFFIX.len())
            .map(|x| *x as u8)
            .ne(SELFDELETE_SUFFIX.as_bytes().iter().rev().copied())
    {
        return;
    }

    // The file we want to delete, is the first argument to the deletion executable
    // This is abit odd.  This operation can fail, but there is really nothing we can
    // do to report it, so might as well not even try.  But from this point onwards
    // we close the process down and will not try to continue regular execution.
    let mut argc = 0;
    let argv = CommandLineToArgvW(GetCommandLineW(), &mut argc);
    if argv.is_null() {
        ExitProcess(1);
    }
    if argc != 3 {
        LocalFree(argv as _);
        ExitProcess(1);
    }
    let parent_process_handle = _wtoi64(*argv.add(1)) as HANDLE;
    let real_filename = *argv.add(2);
    let wait_rv = WaitForSingleObject(parent_process_handle, INFINITE);
    let failed = wait_rv != WAIT_OBJECT_0 || DeleteFileW(real_filename) == 0;
    LocalFree(argv as _);

    if failed {
        ExitProcess(1);
    }

    // hack to make the system pick up on DELETE_ON_CLOSE.  For that purpose we
    // spawn a built-in executable.  This just needs to live long enough that
    // something picks up our inherited handles and we are shut down in
    // between.  This currently uses cmd.exe which should always be available
    // and triggers an immediate shutdown.  The `tmp_exe` handle them moves into
    // that process where it will be finally closed, deleting the file.
    let mut pi: PROCESS_INFORMATION = mem::zeroed();
    let mut si: STARTUPINFOA = mem::zeroed();

    // the CreateProcess family of functions wants a mutable pointer to the
    // cmdline to play around with.  The unicode version is known to do so,
    // the ANSI version does not but it really needs a copy
    cstrdup!(cmdline, b"cmd.exe /c exit\x00");
    si.cb = mem::size_of::<STARTUPINFOA>() as _;
    CreateProcessA(
        ptr::null(),
        cmdline.as_mut_ptr(),
        ptr::null(),
        ptr::null(),
        1,
        CREATE_NO_WINDOW,
        ptr::null(),
        ptr::null(),
        &si,
        &mut pi,
    );

    ExitProcess(0);
}

/// Schedules the deleting of the given executable at shutdown.
///
/// The executable to be deleted has to be valid and have the necessary
/// code in it to perform self deletion.
fn schedule_self_deletion_on_shutdown(
    exe: &Path,
    protected_path: Option<&Path>,
) -> Result<(), io::Error> {
    let first_choice = env::temp_dir();
    let relocated_exe = get_temp_executable_name(&first_choice, RELOCATED_SUFFIX);
    if fs::rename(exe, &relocated_exe).is_ok() {
        let tmp_exe = get_temp_executable_name(&first_choice, SELFDELETE_SUFFIX);
        fs::copy(&relocated_exe, &tmp_exe)?;
        spawn_tmp_exe_to_delete_parent(tmp_exe, relocated_exe)?;
    } else if let Some(protected_path) = protected_path {
        let path = protected_path.parent().ok_or_else(|| {
            io::Error::new(io::ErrorKind::InvalidInput, "protected path has no parent")
        })?;

        let tmp_exe = get_temp_executable_name(path, SELFDELETE_SUFFIX);
        let relocated_exe = get_temp_executable_name(path, RELOCATED_SUFFIX);
        fs::copy(exe, &tmp_exe)?;
        fs::rename(exe, &relocated_exe)?;
        spawn_tmp_exe_to_delete_parent(tmp_exe, relocated_exe)?;
    } else {
        let tmp_exe = get_temp_executable_name(get_directory_of(exe)?, SELFDELETE_SUFFIX);
        fs::copy(exe, &tmp_exe)?;
        spawn_tmp_exe_to_delete_parent(tmp_exe, exe.to_path_buf())?;
    }
    Ok(())
}

// This creates a temporary executable with a random name in the given directory and
// the provided suffix.
fn get_temp_executable_name(base: &Path, suffix: &str) -> PathBuf {
    let mut rng = fastrand::Rng::new();
    let mut file_name = String::new();
    file_name.push('.');

    if let Some(hint) = env::current_exe()
        .ok()
        .as_ref()
        .and_then(|x| x.file_stem())
        .and_then(|x| x.to_str())
    {
        file_name.push_str(hint);
        file_name.push('.');
    }

    for _ in 0..32 {
        file_name.push(rng.lowercase());
    }
    file_name.push_str(suffix);
    base.join(file_name)
}

fn get_directory_of(p: &Path) -> Result<&Path, io::Error> {
    p.parent()
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "path has no parent"))
}

/// The logic here is a bit like the following:
///
/// 1. First we create a copy of our executable in a way that we can actually make it
///    spawn.  This means we put it next to the current binary, with a name that is
///    unlikely going to clash and where we can reproduce the original name from.
/// 2. The copied executable itself is marked so it gets deleted when windows no longer
///    needs the file (`DELETE_ON_CLOSE`)
/// 3. Then we spawn the copy of that executable with a flag that we can pick up in
///    `self_delete_on_init`.  All of this logic is delayed until the process
///    actually shuts down.
/// 4. In `self_delete_on_init` spawn a dummy process so that windows deletes the
///    copy too.
pub fn self_delete(exe: &Path, protected_path: Option<&Path>) -> Result<(), io::Error> {
    schedule_self_deletion_on_shutdown(exe, protected_path)?;
    Ok(())
}

/// This is similar to self_delete, but first renames the executable to a new temporary
/// location so that the executable can be updated by the given other one.
pub fn self_replace(new_executable: &Path) -> Result<(), io::Error> {
    let exe = env::current_exe()?.canonicalize()?;
    let old_exe = get_temp_executable_name(get_directory_of(&exe)?, RELOCATED_SUFFIX);
    fs::rename(&exe, &old_exe)?;
    schedule_self_deletion_on_shutdown(&old_exe, None)?;
    let temp_exe = get_temp_executable_name(get_directory_of(&exe)?, TEMP_SUFFIX);
    fs::copy(new_executable, &temp_exe)?;
    fs::rename(&temp_exe, &exe)?;
    Ok(())
}
