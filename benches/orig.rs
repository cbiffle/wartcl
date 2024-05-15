use criterion::{criterion_group, criterion_main, Criterion};

pub fn benchmark(c: &mut Criterion) {
    c.bench_function("orig eval(subst hello)", |b| {
        let mut tcl = orig::create();
        b.iter(move || {
            let r = tcl.eval(c"subst hello\n");
            assert_eq!(r, 1);
        })
    });
    c.bench_function("orig nested-ifs", |b| {
        let mut tcl = orig::create();
        b.iter(move || {
            let r = tcl.eval(c"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}\n");
            assert_eq!(r, 1);
        })
    });
    c.bench_function("orig complex-expr", |b| {
        let mut tcl = orig::create();
        b.iter(move || {
            let r = tcl.eval(c"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]\n");
            assert_eq!(r, 1);
        })
    });
    c.bench_function("orig call-proc", |b| {
        let mut tcl = orig::create();
        tcl.eval(c"proc testproc {x y z} { }\n");
        b.iter(move || {
            let r = tcl.eval(c"testproc a b c\n");
            assert_eq!(r, 1);
        })
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
