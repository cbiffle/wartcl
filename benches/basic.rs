use criterion::{criterion_group, criterion_main, Criterion};
use wartcl::Val;

pub fn benchmark(c: &mut Criterion) {
    c.benchmark_group("eval(subst hello)")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"subst hello"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"subst hello");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("nested-ifs")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"if {== 0 0} {if {== 0 0} {if {== 0 0} {}}}");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("complex-expr")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("call-proc")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            tcl.eval(Val::from_static(b"proc testproc {x y z} { }")).unwrap();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"testproc a b c"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            tcl.eval(c"proc testproc {x y z} { }");
            b.iter(move || {
                let r = tcl.eval(c"testproc a b c");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("recursive-fib-5")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            tcl.eval(Val::from_static(b"\
                proc fib {x} { \
                    if {<= $x 1} {return 1} else { \
                        return [+ [fib [- $x 1]] [fib [- $x 2]]] \
                    } \
                }")).unwrap();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"fib 5"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            tcl.eval(c"\
                proc fib {x} { \
                    if {<= $x 1} {return 1} { \
                        return [+ [fib [- $x 1]] [fib [- $x 2]]] \
                    } \
                }");
            b.iter(move || {
                let r = tcl.eval(c"fib 5");
                assert_eq!(r, 1);
            })
        });
    // Don't really have any benchmarks testing variable binding and access, so
    // here we go.
    //
    // 45 is the largest fibonacci sequence number that can be represented in
    // our i32 integer type.
    c.benchmark_group("iterative-fib-45")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            tcl.eval(Val::from_static(b"\
                proc fib {x} { \
                    set a 0; \
                    set b 1; \
                    while {!= $x 0} { \
                        set x [- $x 1] ; \
                        set t $b; \
                        set b [+ $a $b]; \
                        set a $t \
                    }; return $a \
                }")).unwrap();
            b.iter(move || {
                let r = tcl.eval(Val::from_static(b"fib 45"));
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            tcl.eval(c"\
                proc fib {x} { \
                    set a 0; \
                    set b 1; \
                    while {!= $x 0} { \
                        set x [- $x 1] ; \
                        set t $b; \
                        set b [+ $a $b]; \
                        set a $t \
                    }; return $a \
                }");
            b.iter(move || {
                let r = tcl.eval(c"fib 45");
                assert_eq!(r, 1);
            })
        });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
