use anyhow::{Result, bail};
use syn::FnArg;

#[derive(Debug)]
pub struct DesugaredSpec {
    pub signature_args: Option<String>,
    pub extra_args: Vec<String>, // e.g., (h_safe : ...)
    pub body: String,
}

pub fn desugar_spec(
    spec_content: &str,
    fn_name: &str,
    args: &[FnArg],
    is_stateful: bool,
) -> Result<DesugaredSpec> {
    let mut extra_args = Vec::new();
    let mut signature_args = None;
    let lines = spec_content.lines().map(|l| l.trim()).filter(|l| !l.is_empty());

    let mut ensures_clause = None;
    let mut logic_lines = Vec::new();

    // Naive line-by-line parsing
    for line in lines {
        if let Some(req) = line.strip_prefix("requires") {
            extra_args.push(format!("({})", req.trim()));
        } else if let Some(ens) = line.strip_prefix("ensures") {
            if ensures_clause.is_some() {
                bail!("Multiple ensures clauses not supported yet");
            }
            ensures_clause = Some(ens.trim().to_string());
        } else if signature_args.is_none() && extra_args.is_empty() && ensures_clause.is_none() {
            // Check if this file looks like signature args.
            // It might be `(x y : Usize)` or `add_mod (x y : Usize)`.
            // We also support instance arguments like `[Layout T]`.
            if let Some(start_idx) = line.find(['(', '[']) {
                // Assume everything from start_idx onwards is args.
                // And ignore what's before it (likely function name).
                signature_args = Some(line[start_idx..].to_string());
            } else {
                // No parenthesis? treat as logic?
                logic_lines.push(line);
            }
        } else {
            logic_lines.push(line);
        }
    }

    // Construct body
    // If ensures |ret, x_final| ...
    let body = if let Some(ens) = ensures_clause {
        // Parse binders |...|
        let (binders, logic) = parse_binders(&ens)?;
        let user_logic = if !logic_lines.is_empty() {
            // Maybe prepend logic lines?
            // Actually currently valid syntax is usually `ensures |...| logic`.
            // `logic_lines` might be empty or continuations.
            // Let's assume `logic` from ensures line + `logic_lines` joined.
            let mut full = logic;
            for l in logic_lines {
                full.push_str("\n  ");
                full.push_str(l);
            }
            full
        } else {
            logic
        };

        generate_body(fn_name, args, is_stateful, &binders, &user_logic)?
    } else {
        // No ensures clause.
        // check if we have logic lines
        if !logic_lines.is_empty() {
            bail!(
                "Raw spec lines not supported. Use 'ensures |...| ...'.\nFound: {:?}",
                logic_lines
            );
        } else {
            "True".to_string()
        }
    };

    Ok(DesugaredSpec { signature_args, extra_args, body })
}

fn parse_binders(ensures_content: &str) -> Result<(Vec<String>, String)> {
    // |ret, x_final| logic
    if let Some(start) = ensures_content.find('|')
        && let Some(end) = ensures_content[start + 1..].find('|')
    {
        let binders_str = &ensures_content[start + 1..start + 1 + end];
        let logic = &ensures_content[start + 1 + end + 1..];
        let binders = binders_str
            .split(',')
            .map(|s| s.trim().to_string())
            .filter(|s| !s.is_empty())
            .collect();
        return Ok((binders, logic.trim().to_string()));
    }
    bail!("Malformed ensures clause: missing |...| binders");
}

fn generate_body(
    fn_name: &str,
    input_args: &[FnArg],
    is_stateful: bool,
    binders: &[String],
    logic: &str,
) -> Result<String> {
    let mut out = String::new();

    // 1. Quantifiers
    // "exists ret x_final,"
    if !binders.is_empty() {
        out.push_str("exists");
        for b in binders {
            if b != "_" {
                out.push(' ');
                out.push_str(b);
            } else {
                // If it's "_", we usually need a name for the exists,
                // but if the user didn't name it, maybe we auto-name it?
                // Or Aeneas requires a name.
                // Let's generate a temp name if needed or just skip?
                // Lean `exists _, ...` is valid but we need to bind it in the equality check.
                // Wait, `exists ret` -> `fwd ... = Result.ok ret`.
                // If user put `_`, we can't name it in the equality check easily.
                // Let's assume user gives names for now.
                out.push_str(" _");
            }
        }
        out.push_str(",\n  ");
    }

    // Capture argument names for function calls
    let arg_names = input_args
        .iter()
        .map(|arg| match arg {
            FnArg::Typed(pat) => {
                if let syn::Pat::Ident(pat_ident) = &*pat.pat {
                    pat_ident.ident.to_string()
                } else {
                    "_".to_string()
                }
            }
            FnArg::Receiver(_) => "self".to_string(),
        })
        .collect::<Vec<_>>()
        .join(" ");

    // 2. Fwd Check
    // "fn_fwd args = Result.ok ret /\"
    // The first binder is usually the return value.
    if let Some(ret_binder) = binders.first() {
        let fn_call_name =
            if is_stateful { format!("{}_fwd", fn_name) } else { fn_name.to_string() };

        if ret_binder != "_" {
            out.push_str(&format!(
                "{} {} = Result.ok {} /\\\n  ",
                fn_call_name, arg_names, ret_binder
            ));
        } else {
            // exists _, ... = Result.ok _
            out.push_str(&format!(
                "exists v, {} {} = Result.ok v /\\\n  ",
                fn_call_name, arg_names
            ));
        }
    }

    // 3. Back Check (if stateful)
    if is_stateful {
        // We assume remaining binders are for mutable args in order?
        // User prompt: `|ret, x_final|`.
        // Need to know WHICH arg corresponds to `x_final`.
        // "If the function is "Stateful" ... append `/\ func_back args = Result.ok x_final`."
        // "Autonomy Rule: If ... ambiguous ... default to generating a conjunction of *all* backward functions found"
        // This suggests we might need to know the *names* of the back functions.
        // Aeneas generates `fn_back` or `fn_back0`, `fn_back1` etc.
        // If there is only one mutable arg, it is `fn_back`.
        // If detection of back function names is hard without reading Aeneas output,
        // we might guess `fn_back`.
        //
        // Let's assume simple case (one mutable arg) -> `fn_back`.
        // If multiple binders, we might need `fn_back` returning a tuple?
        // Aeneas: "def choose_back ... : Result (T x T)"
        // So `fn_back` returns a tuple if multiple.

        if binders.len() > 1 {
            let back_binders = &binders[1..]; // ret is 0

            // If just one back binder, easy.
            if back_binders.len() == 1 {
                out.push_str(&format!(
                    "{}_back {} = Result.ok {} /\\\n  ",
                    fn_name, arg_names, back_binders[0]
                ));
            } else {
                // Tuple return
                // {}_back {} = Result.ok (b1, b2, ...)
                let tuple_inner = back_binders.join(", ");
                out.push_str(&format!(
                    "{}_back {} = Result.ok ({}) /\\\n  ",
                    fn_name, arg_names, tuple_inner
                ));
            }
        }
    }

    // 4. User Logic
    out.push_str(&format!("({})", logic));

    // 5. Automatic Validity Invariants
    // For every binder we exposed (ret, x_final, etc.), we enforce logical validity.
    // "Component 4 ... Return Value Injection ... Mutable Borrow Injection"
    // "Action: Append the validity check ... Result: ... /\ Verifiable.is_valid ret"
    for binder in binders {
        if binder != "_" {
            out.push_str(&format!(" /\\ Verifiable.is_valid {}", binder));
        }
    }

    Ok(out)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_reject_raw_spec() {
        let spec = "some raw logic line\n another line";
        let args = Vec::new();
        let res = desugar_spec(spec, "test_fn", &args, false);
        assert!(res.is_err());
        assert!(res.unwrap_err().to_string().contains("Raw spec lines not supported"));
    }

    #[test]
    fn test_accept_ensures() {
        let spec = "ensures |ret| ret = x";
        let args = Vec::new();
        let res = desugar_spec(spec, "test_fn", &args, false);
        assert!(res.is_ok());
    }

    #[test]
    fn test_accept_requires_only() {
        let spec = "requires h : x > 0";
        let args = Vec::new();
        let res = desugar_spec(spec, "test_fn", &args, false);
        assert!(res.is_ok());
        assert_eq!(res.unwrap().body, "True");
    }
}
