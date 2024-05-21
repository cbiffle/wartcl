use super::*;

/// Implementation of the `set` standard command.
pub fn cmd_set(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let name = mem::take(&mut tcl.commandstack[frame + 1]);
    if let Some(new_value) = tcl.commandstack.get_mut(frame + 2) {
        let new_value = mem::take(new_value);
        tcl.set_or_create_var(&name, new_value.clone());
        Ok(new_value)
    } else {
        tcl.get_existing_var(&name).ok_or(FlowChange::Error)
    }
}

/// Implementation of the `subst` standard command.
pub fn cmd_subst(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let arg = mem::take(&mut tcl.commandstack[frame + 1]);
    match tcl.subst(arg)? {
        DelayedEval::Ready(v) => Ok(v),
        DelayedEval::EvalThis(v) => tcl.eval(v),
    }
}

#[cfg(feature = "incr")]
pub fn cmd_incr(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let name = mem::take(&mut tcl.commandstack[frame + 1]);
    let current_int = tcl.get_existing_var(&name)
        .map(|v| int(&v))
        .unwrap_or(0);
    let new = int_value(current_int + 1);
    tcl.set_or_create_var(&name, new.clone());
    Ok(new)
}

/// Implementation of the `puts` standard command.
#[cfg(any(test, feature = "std"))]
pub fn cmd_puts(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    println!("{}", String::from_utf8_lossy(&tcl.commandstack[frame + 1]));
    Ok(empty())
}

/// Implementation of the `proc` standard command.
#[cfg(feature = "proc")]
pub fn cmd_proc(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let body = mem::take(&mut tcl.commandstack[frame + 3]);
    let name = mem::take(&mut tcl.commandstack[frame + 1]);

    let parsed_params = parse_list(mem::take(&mut tcl.commandstack[frame + 2]));

    tcl.register(name, 0, move |tcl, act_frame| {
        tcl.scope.parent = Some(Box::new(mem::take(&mut tcl.scope)));

        for (i, param) in parsed_params.iter().enumerate() {
            let v = mem::take(tcl.commandstack.get_mut(act_frame + i + 1).ok_or(FlowChange::Error)?);
            tcl.set_or_create_var(param, v);
        }
        let r = tcl.eval(body.clone());

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
pub fn cmd_if(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let mut branch = None;

    // Skip the first argument.
    let mut i = frame + 1;
    // We always arrive at the top of this loop while expecting a condition,
    // either just after the initial "if", or after an "elseif".
    while i < tcl.commandstack.len() {
        let cond = mem::take(&mut tcl.commandstack[i]);
        let cond = int(&tcl.eval(cond)?) != 0;

        if cond {
            branch = Some(mem::take(&mut tcl.commandstack[i + 1]));
            break;
        }

        i += 2;

        if let Some(next) = tcl.commandstack.get(i) {
            match &**next {
                b"else" => {
                    branch = Some(mem::take(&mut tcl.commandstack[i + 1]));
                    break;
                }
                b"elseif" => {
                    // Return error if elseif is the last token.
                    if i + 1 == tcl.commandstack.len() {
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
pub fn cmd_while(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let body = mem::take(&mut tcl.commandstack[frame + 2]);

    let cond = mem::take(&mut tcl.commandstack[frame + 1]);

    debug!("while body = {:?}", String::from_utf8_lossy(&body));
    loop {
        if int(&tcl.eval(cond.clone())?) == 0 {
            break;
        }
        let r = tcl.eval(body.clone());
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
/// choose the operation.
#[cfg(any(feature = "arithmetic", feature = "comparison"))]
pub fn cmd_math(tcl: &mut Env, frame: usize) -> Result<Val, FlowChange> {
    let (a, b) = {
        let bval = mem::take(&mut tcl.commandstack[frame + 2]);
        let aval = mem::take(&mut tcl.commandstack[frame + 1]);
        (int(&aval), int(&bval))
    };

    let c = match &*mem::take(&mut tcl.commandstack[frame]) {
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
type StaticCmd = fn(&mut Env, usize) -> Result<Val, FlowChange>;

static STANDARD_COMMANDS: &[(&Value, usize, StaticCmd)] = &[
    // So far I consider these commands universal, and haven't felt the need to
    // make them optional. That could be changed.
    (b"set", 0, cmd_set),
    (b"subst", 2, cmd_subst),
    (b"if", 0, cmd_if),
    (b"while", 3, cmd_while),
    (b"break", 1, |_, _| Err(FlowChange::Break)),
    (b"continue", 1, |_, _| Err(FlowChange::Again)),
    (b"return", 0, |tcl, frame| {
        Err(FlowChange::Return(
            tcl.commandstack.get_mut(frame + 1).map(mem::take).unwrap_or_default()
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
/// The exact commands registered depend on the build options.
pub fn register_all(env: &mut Env) {
    for &(name, arity, function) in STANDARD_COMMANDS {
        env.register(Val::from_static(name), arity, function);
    }
}
