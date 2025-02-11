use criterion::{criterion_group, criterion_main, Criterion};
use wartcl::FlowChange;

pub fn benchmark(c: &mut Criterion) {
    c.benchmark_group("return")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(b"return hello");
                if let Err(FlowChange::Return(_)) = r {
                    // yay
                } else {
                    panic!("expected return, got: {r:?}");
                }
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"return");
                assert_eq!(r, 2);
            })
        });
    c.benchmark_group("nested-ifs")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(b"\
                    if {== 0 0} {
                        if {== 0 0} {
                            if {== 0 0} {
                            }
                        }
                    }"
                );
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            b.iter(move || {
                let r = tcl.eval(c"\
                    if {== 0 0} {
                        if {== 0 0} {
                            if {== 0 0} {
                            }
                        }
                    }"
                );
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("complex-expr")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            b.iter(move || {
                let r = tcl.eval(b"set a 5; set b 7; subst [- [* 4 [+ $a $b]] t]");
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
            tcl.eval( b"proc testproc1 {x y z} { testproc2 g h i }").unwrap();
            tcl.eval( b"proc testproc2 {x y z} { testproc3 d e f }").unwrap();
            tcl.eval( b"proc testproc3 {x y z} { }").unwrap();
            b.iter(move || {
                let r = tcl.eval(b"testproc1 a b c");
                assert!(r.is_ok());
            })
        })
        .bench_function("partcl", |b| {
            let mut tcl = partcl_wrapper::create();
            tcl.eval(c"proc testproc1 {x y z} { testproc2 g h i }");
            tcl.eval(c"proc testproc2 {x y z} { testproc3 d e f }");
            tcl.eval(c"proc testproc3 {x y z} { }");
            b.iter(move || {
                let r = tcl.eval(c"testproc1 a b c");
                assert_eq!(r, 1);
            })
        });
    c.benchmark_group("recursive-fib-5")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            tcl.eval(b"\
                proc fib {x} { \
                    if {<= $x 1} {return 1} else { \
                        return [+ [fib [- $x 1]] [fib [- $x 2]]] \
                    } \
                }").unwrap();
            b.iter(move || {
                let r = tcl.eval(b"fib 5");
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
            tcl.eval(b"\
                proc fib {x} { \
                    set a 0; \
                    set b 1; \
                    while {!= $x 0} { \
                        set x [- $x 1] ; \
                        set t $b; \
                        set b [+ $a $b]; \
                        set a $t \
                    }; return $a \
                }").unwrap();
            b.iter(move || {
                let r = tcl.eval(b"fib 45");
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
    c.benchmark_group("incr")
        .bench_function("wartcl", |b| {
            let mut tcl = wartcl::Env::default();
            tcl.eval(b"\
                proc test {} { \
                    set x 0; \
                    while {< $x 1000} { \
                        incr x; \
                    }; \
                }").unwrap();
            b.iter(move || {
                let r = tcl.eval(b"test");
                assert!(r.is_ok());
            })
        });
}

criterion_group!(benches, benchmark);
criterion_main!(benches);
