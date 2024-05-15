fn main() {
    // TODO: it is not clear why I need to do this by hand, one would think the
    // cc crate would be doing it.
    println!("cargo::rerun-if-changed=src/tcl.c");

    cc::Build::new()
        .file("src/tcl.c")
        .compile("partcl");
}
