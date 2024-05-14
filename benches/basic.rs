use criterion::{criterion_group, criterion_main, Criterion};

pub fn benchmark(c: &mut Criterion) {
    c.bench_function("eval(subst hello)", |b| {
        let mut tcl = partclish::init();
        b.iter(move || {
            let r = partclish::eval(&mut tcl, b"subst hello\n");
            assert_eq!(r, partclish::Flow::Normal);
        })
    });
    c.bench_function("nested-ifs", |b| {
        let mut tcl = partclish::init();
        b.iter(move || {
            let r = partclish::eval(&mut tcl, b"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}\n");
            assert_eq!(r, partclish::Flow::Normal);
        })
    });
    c.bench_function("complex-expr", |b| {
        let mut tcl = partclish::init();
        b.iter(move || {
            let r = partclish::eval(&mut tcl,
                b"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]\n");
            assert_eq!(r, partclish::Flow::Normal);
        })
    });
    c.bench_function("call-proc", |b| {
        let mut tcl = partclish::init();
        partclish::eval(&mut tcl, b"proc testproc {x y z} { }\n");
        b.iter(move || {
            let r = partclish::eval(&mut tcl,
                b"testproc a b c\n");
            assert_eq!(r, partclish::Flow::Normal);
        })
    });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
