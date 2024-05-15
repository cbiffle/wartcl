fn main() {
    cc::Build::new()
        .file("src/tcl.c")
        .compile("partcl");
}
