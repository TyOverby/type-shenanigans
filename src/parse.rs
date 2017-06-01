use snoot;
use snoot::Sexpr;
use snoot::parse::Span;
use snoot::token::{ListType, TokenType};
use snoot::diagnostic::DiagnosticBag;
use super::{Type, FunctionType, RecordType};

use std::collections::HashMap;


pub fn parse(text: &str) -> Vec<Type> {
    let snoot::Result { roots, mut diagnostics } = snoot::simple_parse(text, &[":"], Some("<text>"));
    let mut out = vec![];

    for root in roots {
        match trx(&root) {
            Ok(typ) => out.push(typ),
            Err(es) => diagnostics.append(es),
        }
    }

    diagnostics.assert_no_errors();
    out
}

pub fn parse_one(text: &str) -> Type {
    let out = parse(text);
    assert!(out.len() == 1);
    out.into_iter().next().unwrap()
}

pub fn trx(sexpr: &Sexpr) -> Result<Type, DiagnosticBag> {
    match sexpr {
        &Sexpr::Terminal(_, ref span) => {
            match &*span.text() {
                "number" => Ok(Type::Number),
                "boolean" => Ok(Type::Boolean),
                o => {
                    Err(DiagnosticBag::singleton(diagnostic!(span, "{} is not a type", o)))
                }
            }
        }
        &Sexpr::List { ref opening_token, ref children, ref span, .. }
        if opening_token.typ == TokenType::ListOpening(ListType::Brace) => {
            if children.len() % 3 != 0 {
                Err(DiagnosticBag::singleton(diagnostic!(span, "invalid record declaration")))
            } else {
                let mut builder = HashMap::new();
                let mut errors = DiagnosticBag::new();
                for field in children.chunks(3)
                    .map(|pair| parse_field(&pair[0], &pair[1], &pair[2])) {
                    match field {
                        Ok((s, t)) => {
                            if builder.contains_key(&s) {
                                errors.add(diagnostic!(span, "duplicate record name {} in struct", s));
                            } else {
                                builder.insert(s, t);
                            }
                        }
                        Err(es) => {
                            errors.append(es);
                        }
                    }
                }
                if errors.is_empty() {
                    Ok(Type::Record(RecordType::Record{ fields: builder }))
                } else {
                    Err(errors)
                }
            }
        }
        &Sexpr::List { ref children, ref span, .. } => {
            if children.is_empty() {
                Err(DiagnosticBag::singleton(diagnostic!(span, "what are you doing with this empty list")))
            } else {
                match &children[0] {
                    &Sexpr::Terminal(_, ref span) if &*span.text() == "union" =>
                        parse_union(&children[1..], span),
                    &Sexpr::Terminal(_, ref span) if &*span.text() == "intersect" =>
                        parse_intersection(&children[1..], span),
                    &Sexpr::Terminal(_, ref span) if &*span.text() == "fn" =>
                        parse_function_body(&children[1..], span),
                    other => {
                        Err(DiagnosticBag::singleton(diagnostic!(other.span(), "{} unexpected", other.span().text())))
                    }
                }
            }
        }
        &Sexpr::String(_, ref span) => {
            Err(DiagnosticBag::singleton(diagnostic!(span, "strings are not allowed")))
        }
        &Sexpr::UnaryOperator { ref span, .. } => {
            Err(DiagnosticBag::singleton(diagnostic!(span, "unary operators are not allowed")))
        }
    }
}

fn parse_field<'a>(name: &Sexpr, colon: &Sexpr, typ: &Sexpr) -> Result<(String, Type), DiagnosticBag> {
    let mut errors = DiagnosticBag::new();
    let name = if let &Sexpr::Terminal(_, ref span) = name {
        span.text().to_string()
    } else {
        errors.add(diagnostic!(name.span(), "expected name of struct"));
        "".to_string()
    };

    if let &Sexpr::Terminal(_, ref span) = colon {
        if &*span.text() != ":" {
            errors.add(diagnostic!(span, "expected :"));
        }
    } else {
        errors.add(diagnostic!(colon.span(), "expected :"));
    }

    let typ = match trx(typ) {
        Ok(typ) => typ,
        Err(errs) => {
            errors.append(errs);
            Type::Boolean
        }
    };

    if !errors.is_empty() {
        return Err(errors);
    }

    Ok((name, typ))
}

fn parse_union(bodies: &[Sexpr], span: &Span) -> Result<Type, DiagnosticBag> {
    match bodies.len() {
        0 | 1 => {
            Err(DiagnosticBag::singleton(diagnostic!(span, "union with {} members", bodies.len())))
        }
        2 => {
            let left = trx(&bodies[0])?;
            let right = trx(&bodies[1])?;
            Ok(left.union_with(right))
        }
        _ => {
            let left = trx(&bodies[0])?;
            let right = parse_union(&bodies[1..], span)?;
            Ok(left.union_with(right))
        }
    }
}

fn parse_intersection(bodies: &[Sexpr], span: &Span) -> Result<Type, DiagnosticBag> {
    match bodies.len() {
        0 | 1 => {
            Err(DiagnosticBag::singleton(diagnostic!(span, "intersection with {} members", bodies.len())))
        }
        2 => {
            let left = trx(&bodies[0])?;
            let right = trx(&bodies[1])?;
            Ok(left.intersect_with(right))
        }
        _ => {
            let left = trx(&bodies[0])?;
            let right = parse_intersection(&bodies[1..], span)?;
            Ok(left.intersect_with(right))
        }
    }
}

fn parse_function_body(bodies: &[Sexpr],
                           span: &Span)
                           -> Result<Type, DiagnosticBag> {
    match bodies.len() {
        0 | 1 | 2 => {
            Err(DiagnosticBag::singleton(diagnostic!(span, "invalid function type")))
        }
        3 => {
            let arg = trx(&bodies[0])?;
            let ret = trx(&bodies[2])?;
            if let &Sexpr::Terminal(_, ref span) = &bodies[1] {
                if &*span.text() != "->" {
                    return Err(DiagnosticBag::singleton(diagnostic!(span, "expected -> found {}", span.text())));
                }
            }
            Ok(Type::Function(FunctionType::Function {
                arg: Box::new(arg),
                ret: Box::new(ret),
            }))
        }
        _ => {
            let arg = trx(&bodies[0])?;
            let ret = parse_function_body(&bodies[1..], span)?;
            Ok(Type::Function(FunctionType::Function {
                arg: Box::new(arg),
                ret: Box::new(ret),
            }))
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
               vec![Type::Function(FunctionType::Function{
                        arg: Box::new(Type::Number),
                        ret: Box::new(Type::Boolean),
                    })]);
}

#[test]
fn more_complex_function() {
    assert_eq!(parse("(fn number number -> boolean)"),
               vec![Type::Function(FunctionType::Function {
                        arg: Box::new(Type::Number),
                        ret: Box::new(Type::Function(FunctionType::Function{
                            arg: Box::new(Type::Number),
                            ret: Box::new(Type::Boolean),
                        })),
                    })]);
}

#[test]
fn basic_struct() {
    assert_eq!(parse("{}"), vec![Type::Record(RecordType::Record{ fields: HashMap::new() })]);
    assert_eq!(parse("{a: boolean}"), vec![Type::Record(RecordType::Record{ fields: vec![("a".into(), Type::Boolean)].into_iter().collect() })]);
    assert_eq!(parse("{a: boolean b: number}"), vec![Type::Record(RecordType::Record{ fields: vec![("b".into(), Type::Number), ("a".into(), Type::Boolean)].into_iter().collect() })]);
}

#[test]
fn test_struct_union() {
    assert_eq!(
        parse_one("(union {a: number} {b: boolean})"),
        parse_one("{a: number}").union_with(parse_one("{b: boolean}")))
}

#[test]
fn test_struct_intersection() {
    assert_eq!(
        parse_one("(intersect {a: number} {b: boolean})"),
        parse_one("{a: number}").intersect_with(parse_one("{b: boolean}")))
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
