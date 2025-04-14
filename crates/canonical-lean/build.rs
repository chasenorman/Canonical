use std::process::Command;

fn main() {
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();

    let output = Command::new("lean")
        .arg("--print-libdir")
        .output()
        .expect("failed to execute lean --print-libdir");
    let libdir = String::from_utf8(output.stdout)
        .expect("non-UTF8 output")
        .trim()
        .to_owned();

    println!("cargo:rustc-link-search=native={}", libdir);
    if target_os == "windows" {
        println!("cargo:rustc-link-lib=dylib=Init_shared");
    } else {
        println!("cargo:rustc-link-lib=dylib=leanshared");
    }
}
