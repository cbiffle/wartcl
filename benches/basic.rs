use criterion::{criterion_group, criterion_main, Criterion};

pub fn benchmark(c: &mut Criterion) {
    c.benchmark_group("eval(subst hello)")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Tcl::init();
            b.iter(move || {
                let r = tcl.eval( b"subst hello\n");
                assert_eq!(r, Ok(()));
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"subst hello\n");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("nested-ifs")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Tcl::init();
            b.iter(move || {
                let r = tcl.eval( b"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}\n");
                assert_eq!(r, Ok(()));
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}\n");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("complex-expr")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Tcl::init();
            b.iter(move || {
                let r = tcl.eval(b"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]\n");
                assert_eq!(r, Ok(()));
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]\n");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("call-proc")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Tcl::init();
            tcl.eval( b"proc testproc {x y z} { }\n").unwrap();
            b.iter(move || {
                let r = tcl.eval(b"testproc a b c\n");
                assert_eq!(r, Ok(()));
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            tcl.eval(c"proc testproc {x y z} { }\n");
            b.iter(move || {
                let r = tcl.eval(c"testproc a b c\n");
                assert_eq!(r, 1);
            })
        });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
