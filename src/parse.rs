use snoot;
use tendril::StrTendril;
use snoot::parse::{Sexpr, Span};
use snoot::error::{Error, ErrorBuilder};
use super::Type;

use std::fmt::Write;
use std::collections::HashMap;


pub fn parse(text: &str) -> Vec<Type> {
    let snoot::parse::ParseResult { roots, diagnostics } = snoot::simple_parse(text.into(), &[":"]);
    let mut out = vec![];
    let mut errors = vec![];

    for diag in diagnostics {
        errors.push(diag.into_error(None));
    }

    for root in roots {
        match trx(&root) {
            Ok(typ) => out.push(typ),
            Err(es) => errors.extend(es),
        }
    }

    if !errors.is_empty() {
        let mut panic_message = String::new();
        for error in errors {
            writeln!(panic_message, "{}\n", error).unwrap();
        }
        panic!(panic_message);
    }

    out
}

pub fn trx(sexpr: &Sexpr<StrTendril>) -> Result<Type, Vec<Error<StrTendril>>> {
    match sexpr {
        &Sexpr::Terminal(ref token, ref span) => {
            match &*token.string {
                "number" => Ok(Type::Number),
                "boolean" => Ok(Type::Boolean),
                o => {
                    let message = format!("{} is not a type", o);
                    let error = ErrorBuilder::new(message, span).build();
                    Err(vec![error])
                }
            }
        }
        &Sexpr::List { ref opening_token, ref children, ref span, .. }
        if &*opening_token.string == "{" => {
            if children.len() % 3 != 0 {
                let message = "invalid record declaration";
                let error = ErrorBuilder::new(message, span).build();
                Err(vec![error])
            } else {
                let mut builder = HashMap::new();
                let mut errors = vec![];
                for field in children.chunks(3)
                    .map(|pair| parse_field(&pair[0], &pair[1], &pair[2])) {
                    match field {
                        Ok((s, t)) => {
                            if builder.contains_key(&s) {
                                errors.push(ErrorBuilder::new(format!("duplicate record name {} in struct", s), span).build());
                            } else {
                                builder.insert(s, t);
                            }
                        }
                        Err(es) => {
                            errors.extend(es);
                        }
                    }
                }
                if errors.is_empty() {
                    Ok(Type::Structure { fields: builder })
                } else {
                    Err(errors)
                }
            }
        }
        &Sexpr::List { ref children, ref span, .. } => {
            if children.is_empty() {
                let message = format!("what are you doing with this empty list?");
                let error = ErrorBuilder::new(message, span).build();
                Err(vec![error])
            } else {
                match &children[0] {
                    &Sexpr::Terminal(ref token, ref span) if &*token.string == "fn" => {
                        let rest = &children[1..];
                        parse_function_body(rest, span)
                    }
                    other => {
                        let message = format!("'{}' unexpected", other.span().text);
                        let error = ErrorBuilder::new(message, other.span()).build();
                        Err(vec![error])
                    }
                }
            }
        }
        &Sexpr::String(_, ref span) => {
            let message = format!("strings are not allowed");
            Err(vec![ErrorBuilder::new(message, span).build()])
        }
        &Sexpr::UnaryOperator { ref span, .. } => {
            let message = format!("unsary operators are not allowed");
            Err(vec![ErrorBuilder::new(message, span).build()])
        }
    }
}

fn parse_field<'a>(name: &Sexpr<StrTendril>, colon: &Sexpr<StrTendril>, typ: &Sexpr<StrTendril>) -> Result<(String, Type), Vec<Error<StrTendril>>> {
    let mut errors = vec![];
    let name = if let &Sexpr::Terminal(ref token, _) = name {
        token.string.to_string()
    } else {
        errors.push(ErrorBuilder::new("expected name of struct", name.span()).build());
        "".to_string()
    };

    if let &Sexpr::Terminal(ref token, ref span) = colon {
        if &*token.string != ":" {
            errors.push(ErrorBuilder::new("expected ':' in struct", span).build());
        }
    } else {
        errors.push(ErrorBuilder::new("expected ':' in struct", colon.span()).build());
    }

    let typ = match trx(typ) {
        Ok(typ) => typ,
        Err(errs) => {
            errors.extend(errs);
            Type::Boolean
        }
    };

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok((name, typ))
}

fn parse_function_body<'a>(bodies: &[Sexpr<StrTendril>],
                           span: &Span<StrTendril>)
                           -> Result<Type, Vec<Error<StrTendril>>> {
    match bodies.len() {
        0 | 1 | 2 => {
            let message = "invalid function type";
            Err(vec![ErrorBuilder::new(message, span).build()])
        }
        3 => {
            let arg = trx(&bodies[0])?;
            let ret = trx(&bodies[2])?;
            if let &Sexpr::Terminal(ref token, ref span) = &bodies[1] {
                if &*token.string != "->" {
                    let message = format!("expected -> found {}", token.string);
                    return Err(vec![ErrorBuilder::new(message, span).build()]);
                }
            }
            Ok(Type::Function {
                arg: Box::new(arg),
                ret: Box::new(ret),
            })
        }
        _ => {
            let arg = trx(&bodies[0])?;
            let ret = parse_function_body(&bodies[1..], span)?;
            Ok(Type::Function {
                arg: Box::new(arg),
                ret: Box::new(ret),
            })
        }
    }
}

#[test]
fn parse_boolean() {
    assert_eq!(parse("boolean"), vec![Type::Boolean]);
}

#[test]
fn parse_number() {
    assert_eq!(parse("number"), vec![Type::Number]);
}

#[test]
fn number_to_boolean() {
    assert_eq!(parse("(fn number -> boolean)"),
               vec![Type::Function {
                        arg: Box::new(Type::Number),
                        ret: Box::new(Type::Boolean),
                    }]);
}

#[test]
fn more_complex_function() {
    assert_eq!(parse("(fn number number -> boolean)"),
               vec![Type::Function {
                        arg: Box::new(Type::Number),
                        ret: Box::new(Type::Function {
                            arg: Box::new(Type::Number),
                            ret: Box::new(Type::Boolean),
                        }),
                    }]);
}

#[test]
fn basic_struct() {
    assert_eq!(parse("{}"), vec![Type::Structure{ fields: HashMap::new() }]);
    assert_eq!(parse("{a: boolean}"), vec![Type::Structure{ fields: vec![("a".into(), Type::Boolean)].into_iter().collect() }]);
    assert_eq!(parse("{a: boolean b: number}"), vec![Type::Structure{ fields: vec![("b".into(), Type::Number), ("a".into(), Type::Boolean)].into_iter().collect() }]);
}

#[test]
#[should_panic]
fn mismatch_paren() {
    parse("{");
}

#[test]
#[should_panic]
fn same_name_for_fields() {
    parse("{a: boolean a: boolean}");
}