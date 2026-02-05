fn main() {
    let () = "escapes stay as backslashes: \t\r\n";
    //~^ ERROR: mismatched types

    let () = r"absolute: C:\foo\file.rs";
    //~^ ERROR: mismatched types
    let () = r"absolute, spaces: C:\foo bar\file.rs";
    //~^ ERROR: mismatched types
    let () = r"absolute, spaces, dir: C:\foo bar\some dir\";
    //~^ ERROR: mismatched types
    let () = r"absolute, spaces, no extension: C:\foo bar\some file";
    //~^ ERROR: mismatched types

    let () = r"relative: foo\file.rs";
    //~^ ERROR: mismatched types

    let () = r"unicode: Ryū\file.rs";
    //~^ ERROR: mismatched types

    let () = r"mixed seperators: C:\foo/../bar\";
    //~^ ERROR: mismatched types

    let () = r"unsupported: foo\bar";
    //~^ ERROR: mismatched types
}
