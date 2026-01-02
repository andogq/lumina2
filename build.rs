fn main() {
    let prefix = if cfg!(target_os = "macos") {
        "/opt/homebrew/opt/llvm@18"
    } else {
        "/usr/lib/llvm-18"
    };

    // println!("cargo::rustc-env=LLVM_SYS_181_PREFIX={prefix}");
}
