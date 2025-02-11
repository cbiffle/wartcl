//! Built-in commands.
//!
//! These are automatically registered in any `Env` created using
//! `Env::default()`. You could also use `Env::empty()` and then call
//! `register_all` to load all of these commands.
//!
//! If you'd like to pick and choose, you can also pass individual functions to
//! `register` by hand.

use super::*;

/// Implementation of the `set` standard command.
pub fn cmd_set(tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    let name = mem::take(&mut args[1]);
    if let Some(new_value) = args.get_mut(2) {
        // `set` _with_ a new value creates or updates a binding, and returns
        // the value, so we must copy.
        tcl.set_or_create_var(name, new_value.clone());
        Ok(mem::take(new_value))
    } else {
        // `set` without a new value returns the contents of an existing
        // binding, or fails if no such binding exists.
        tcl.get_existing_var(&name)
            .map(OwnedValue::from)
            .ok_or(FlowChange::Error)
    }
}

/// Implementation of the `incr` standard command (feature `incr`).
#[cfg(feature = "incr")]
pub fn cmd_incr(tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    let name = mem::take(&mut args[1]);
    // If the binding is missing, `incr` will treat it as containing zero, and
    // create it below.
    let current_int = tcl.get_existing_var(&name)
        .map(int)
        .unwrap_or(0);
    let new = int_value(current_int + 1);
    // Because `incr` returns the updated value, we have to clone the new
    // string.
    tcl.set_or_create_var(name, new.clone());
    Ok(new)
}

/// Implementation of the `puts` standard command (feature `std`).
#[cfg(any(test, feature = "std"))]
pub fn cmd_puts(_tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    println!("{}", String::from_utf8_lossy(&args[1]));
    Ok(empty())
}

/// Implementation of the `proc` standard command (feature `proc`).
#[cfg(feature = "proc")]
pub fn cmd_proc(tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    // Take the body by-val before we start making references into the args list
    // (to do otherwise breaks aliasing rules).
    let body = mem::take(&mut args[3]);

    let name = &args[1];
    let param_names = parse_list(&args[2]);

    tcl.register(name, param_names.len() + 1, move |tcl, args| {
        // Because we've bound this command to a specific arity, the evaluator
        // should check the arg count. If it fails to do so, this assert will
        // trip in tests.
        debug_assert!(args.len() == param_names.len() + 1);

        // Thread a new scope onto the return chain. Since this moves the
        // existing bindings into the heap, we start empty.
        tcl.scope.parent = Some(Box::new(mem::take(&mut tcl.scope)));

        // Bind all parameters in this new scope.
        for (name, val) in param_names.iter().zip(&mut args[1..]) {
            tcl.set_or_create_var(name.clone(), mem::take(val));
        }

        // Run the procedure.
        let r = tcl.eval(&body);

        tcl.scope = *tcl.scope.parent.take().unwrap();

        match r {
            Err(FlowChange::Return(v)) | Ok(v) => Ok(v),
            // Coerce break/continue at top level of proc into error.
            Err(_) => Err(FlowChange::Error),
        }
    });
    Ok(empty())
}

/// Implementation of the `if` standard command.
///
/// `if {condition} {body}`
/// `if {condition} {body} else {body2}`
/// `if {condition} {body} elseif {condition2} {body2} ...`
/// `if {condition} {body} elseif {condition2} {body2} ... else {body3}`
pub fn cmd_if(tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    let mut branch = None;

    // Skip the first argument.
    let mut i = 1;
    // We always arrive at the top of this loop while expecting a condition,
    // either just after the initial "if", or after an "elseif".
    while i < args.len() {
        let cond = int(&tcl.eval(&args[i])?) != 0;

        if cond {
            branch = Some(&*args[i + 1]);
            break;
        }

        i += 2;

        if let Some(next) = args.get(i) {
            match &**next {
                b"else" => {
                    branch = Some(&*args[i + 1]);
                    break;
                }
                b"elseif" => {
                    // Return error if elseif is the last token.
                    if i + 1 == args.len() {
                        return Err(FlowChange::Error);
                    }
                    i += 1;
                }
                _ => return Err(FlowChange::Error),
            }
        }
    }
    tcl.eval(branch.unwrap_or_default())
}

/// Implementation of the `while` standard command.
pub fn cmd_while(tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    let body = mem::take(&mut args[2]);

    let cond = mem::take(&mut args[1]);

    loop {
        if int(&tcl.eval(&cond)?) == 0 {
            break;
        }
        let r = tcl.eval(&body);
        match r {
            Err(FlowChange::Again) | Ok(_) => (),

            Err(FlowChange::Break) => break,
            Err(e) => return Err(e),
        }
    }
    // Standard sez while _always_ returns an empty string.
    Ok(empty())
}

/// Implementation of the standard math commands; parses its first argument to
/// choose the operation (features `arithmetic` or `comparison`).
///
/// The specific list of operators this implements is:
///
/// - With feature `arithmetic`: `+` `-` `*` `/` 
/// - With feature `comparison`: `==` `!=` `<` `<=` `>` `>=`
///
/// You can register this by hand by e.g.
///
/// ```
/// let mut tcl = wartcl::Env::empty();
/// tcl.register(b"+", 3, wartcl::cmd::cmd_math);
/// tcl.register(b"-", 3, wartcl::cmd::cmd_math);
/// // and so on
/// ```
///
/// If you register this command under an unsupported name, it will panic when
/// you use it.
#[cfg(any(feature = "arithmetic", feature = "comparison"))]
pub fn cmd_math(_tcl: &mut Env, args: &mut [OwnedValue]) -> Result<OwnedValue, FlowChange> {
    let bval = &args[2];
    let aval = &args[1];
    let opval = &args[0];

    let a = int(aval);
    let b = int(bval);

    let c = match &**opval {
        #[cfg(feature = "arithmetic")]
        b"+" => a + b,
        #[cfg(feature = "arithmetic")]
        b"-" => a - b,
        #[cfg(feature = "arithmetic")]
        b"*" => a * b,
        #[cfg(feature = "arithmetic")]
        b"/" => a / b,

        #[cfg(feature = "comparison")]
        b">" => (a > b) as Int,
        #[cfg(feature = "comparison")]
        b">=" => (a >= b) as Int,
        #[cfg(feature = "comparison")]
        b"<" => (a < b) as Int,
        #[cfg(feature = "comparison")]
        b"<=" => (a <= b) as Int,
        #[cfg(feature = "comparison")]
        b"==" => (a == b) as Int,
        #[cfg(feature = "comparison")]
        b"!=" => (a != b) as Int,

        _ => panic!(),
    };

    Ok(int_value(c))
}

/// Type of a command implemented with a stateless function pointer, as opposed
/// to a general closure.
pub type StaticCmd = fn(&mut Env, &mut [OwnedValue]) -> Result<OwnedValue, FlowChange>;

/// Fixed table of standard commands, in an unspecified order. The contents
/// depend on the chosen Cargo features.
///
/// Each entry in this table has the form `(name, arity, fnptr)`. All names in
/// this table are guaranteed unique.
///
/// You generally don't need to access this table directly, since `register_all`
/// and `Env::default()` will both do it for you. But in case you're doing
/// something unusual, here you go.
pub static STANDARD_COMMANDS: &[(&Value, usize, StaticCmd)] = &[
    // So far I consider these commands universal, and haven't felt the need to
    // make them optional. That could be changed.
    (b"set", 0, cmd_set),
    (b"if", 0, cmd_if),
    (b"while", 3, cmd_while),
    (b"break", 1, |_, _| Err(FlowChange::Break)),
    (b"continue", 1, |_, _| Err(FlowChange::Again)),
    (b"return", 0, |_tcl, args| {
        Err(FlowChange::Return(
            args.get_mut(1).map(mem::take).unwrap_or_default()
        ))
    }),

    #[cfg(any(test, feature = "std"))]
    (b"puts", 2, cmd_puts),

    #[cfg(feature = "proc")]
    (b"proc", 4, cmd_proc),

    #[cfg(feature = "incr")]
    (b"incr", 2, cmd_incr),

    #[cfg(feature = "arithmetic")]
    (b"+", 3, cmd_math),
    #[cfg(feature = "arithmetic")]
    (b"-", 3, cmd_math),
    #[cfg(feature = "arithmetic")]
    (b"*", 3, cmd_math),
    #[cfg(feature = "arithmetic")]
    (b"/", 3, cmd_math),

    #[cfg(feature = "comparison")]
    (b">", 3, cmd_math),
    #[cfg(feature = "comparison")]
    (b">=", 3, cmd_math),
    #[cfg(feature = "comparison")]
    (b"<", 3, cmd_math),
    #[cfg(feature = "comparison")]
    (b"<=", 3, cmd_math),
    #[cfg(feature = "comparison")]
    (b"==", 3, cmd_math),
    #[cfg(feature = "comparison")]
    (b"!=", 3, cmd_math),
];

/// Registers all standard built-in commands with `env`.
///
/// You do not need to call this if the `env` was created with `Env::default()`.
///
/// The exact commands registered depend on the build options.
pub fn register_all(env: &mut Env) {
    for &(name, arity, function) in STANDARD_COMMANDS {
        env.register(name, arity, function);
    }
}
