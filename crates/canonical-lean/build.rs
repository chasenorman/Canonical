use std::process::Command;

fn default_libdir() -> String {
    let output = Command::new("lean")
        .arg("--print-libdir")
        .output()
        .expect("failed to execute lean --print-libdir");
    String::from_utf8(output.stdout)
        .expect("non-UTF8 output")
        .trim()
        .to_owned()
}

fn main() {
    let target_os = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    // Release artifacts only: `cargo check` (rust-analyzer) shouldn't see this.
    if std::env::var("PROFILE").as_deref() == Ok("release")
        && std::env::var_os("CARGO_FEATURE_HOST_MIMALLOC").is_none()
    {
        println!("cargo:warning=libcanonical_lean built without `host-mimalloc`; \
            for Lean use `build_lean.py` (cargo build -p canonical_lean --features host-mimalloc)");
    }
    let libdir = std::env::var("LEAN_LIBDIR").unwrap_or_else(|_| {
        default_libdir()
    });

    println!("cargo:rustc-link-search=native={}", libdir);
    // Only Windows needs an import library. Elsewhere the Lean runtime symbols
    // are left undefined and bound at load time to the host process, so the
    // library works both in the `lean` server (libleanshared) and in Lake
    // executables that link the runtime statically (`-lleanrt`). Linking
    // libleanshared here would load a second runtime into such executables and
    // its allocator would free objects owned by the other one.
    if target_os == "windows" {
        println!("cargo:rustc-link-lib=dylib=Init_shared");
    }
}
