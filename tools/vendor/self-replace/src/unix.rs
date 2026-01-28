use std::env;
use std::fs;
use std::io;
use std::path::Path;

/// On Unix a running executable can be safely deleted.
pub fn self_delete(exe: &Path) -> Result<(), io::Error> {
    let exe = exe.canonicalize()?;
    fs::remove_file(exe)?;
    Ok(())
}

pub fn self_replace(new_executable: &Path) -> Result<(), io::Error> {
    let mut exe = env::current_exe()?;
    if fs::symlink_metadata(&exe).map_or(false, |x| x.file_type().is_symlink()) {
        exe = fs::read_link(exe)?;
    }
    let old_permissions = exe.metadata()?.permissions();

    let prefix = if let Some(hint) = exe.file_stem().and_then(|x| x.to_str()) {
        format!(".{}.__temp__", hint)
    } else {
        ".__temp__".into()
    };

    let tmp = tempfile::Builder::new()
        .prefix(&prefix)
        .tempfile_in(exe.parent().ok_or_else(|| {
            io::Error::new(
                io::ErrorKind::Other,
                "executable has no known parent folder",
            )
        })?)?;
    fs::copy(new_executable, tmp.path())?;
    fs::set_permissions(tmp.path(), old_permissions)?;

    // if we made it this far, try to persist the temporary file and move it over.
    let (_, path) = tmp.keep()?;
    match fs::rename(&path, &exe) {
        Ok(()) => {}
        Err(err) => {
            fs::remove_file(&path).ok();
            return Err(err);
        }
    }

    Ok(())
}
