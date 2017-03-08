extern crate snoot;
extern crate tendril;

pub mod parse;

use std::cmp::Ordering;

use std::collections::HashMap;

#[derive(Eq, PartialEq, Debug)]
pub enum Type {
    Function {
        arg: Box<Type>,
        ret: Box<Type>,
    },
    Structure {
        fields: HashMap<String, Type>
    },
    Boolean,
    Number,
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Type) -> Option<Ordering> {
        match (self, other) {
            (&Type::Number, &Type::Number) => Some(Ordering::Equal),
            (&Type::Boolean, &Type::Boolean) => Some(Ordering::Equal),
            (&Type::Function{arg: ref a1, ret: ref r1}, &Type::Function{arg: ref a2, ret: ref r2}) => {
                let (c1, c2) = match (a1.partial_cmp(a2), r1.partial_cmp(r2)) {
                    (None, _) => return None,
                    (_, None) => return None,
                    (Some(c1), Some(c2)) => (c1, c2),
                };
                match (c1, c2) {
                    (Ordering::Equal, Ordering::Equal) => Some(Ordering::Equal),

                    (Ordering::Less, Ordering::Less) |
                    (Ordering::Greater, Ordering::Greater) => None,

                    (Ordering::Less, Ordering::Equal) |
                    (Ordering::Less, Ordering::Greater) |
                    (Ordering::Equal, Ordering::Greater) => Some(Ordering::Greater),

                    (Ordering::Greater, Ordering::Equal) |
                    (Ordering::Greater, Ordering::Less) |
                    (Ordering::Equal, Ordering::Less) => Some(Ordering::Less),
                }
            }
            (&Type::Structure {fields: ref f1}, &Type::Structure {fields: ref f2}) => {
                if f1.len() > f2.len() {
                    return other.partial_cmp(self).map(Ordering::reverse);
                }
                let mut found_less = false;
                let mut found_greater = false;
                for (&ref field, &ref typ1) in f1 {
                    match f2.get(field).and_then(|typ2| typ1.partial_cmp(typ2)) {
                        Some(Ordering::Less) => found_less = true,
                        Some(Ordering::Greater) => found_greater = true,
                        Some(Ordering::Equal) => {},
                        None => return None,
                    }
                }
                match (found_less, found_greater, f1.len().cmp(&f2.len())) {
                    (_, _, Ordering::Greater) => unreachable!(),
                    (false, false, Ordering::Equal) => Some(Ordering::Equal),
                    (false, false, Ordering::Less) => Some(Ordering::Greater),
                    (true, false, Ordering::Equal) => Some(Ordering::Less),
                    (true, false, Ordering::Less) => None,
                    (false, true, Ordering::Equal) => Some(Ordering::Greater),
                    (false, true, Ordering::Less) => Some(Ordering::Greater),
                    (true, true, _) => None,
                }
            }
            (_, _) => None
        }
    }
}

#[cfg(test)]
use parse::parse as p;

#[test]
fn subtyping_basic() {
    assert!(Type::Boolean == Type::Boolean);
    assert!(Type::Number == Type::Number);
    assert!(Type::Number != Type::Boolean);
}

#[test]
fn subtyping_structs() {
    assert!(p("{}") == p("{}"));

    assert!(p("{a: number}") != p("{}"));
    assert!(p("{a: number}") < p("{}"));
    assert!(p("{}") > p("{a: number}"));

    assert!(p("{a: number b: boolean}") != p("{b: boolean}"));
    assert!(p("{a: number b: boolean}") < p("{b: boolean}"));
    assert!(p("{b: boolean}") > p("{a: number b: boolean}"));

    assert!(p("{a: number}") != p("{a: boolean}"));
    assert_eq!(p("{a: number}").partial_cmp(&p("{a: boolean}")), None);
    assert_eq!(p("{a: boolean}").partial_cmp(&p("{a: number}")), None);

    assert!(p("{a: {}}") == p("{a: {}}"));

    assert_eq!(p("{a: {b: number}}").partial_cmp(&p("{a: {b: boolean}}")), None);

    assert!(p("{a: {b: number}}") == p("{a: {b: number}}"));

    assert!(p("{a: {b: number}}") != p("{a: {}}"));
    assert!(p("{a: {b: number}}") < p("{a: {}}"));
    assert!(p("{a: {}}") > p("{a: {b: number}}"));

    assert_eq!(p("{a: {b: number}}").partial_cmp(&p("{a: {c: boolean}}")), None);

    assert!(p("{a: {b: number} c: boolean}") != p("{a: {b: number}}"));
    assert!(p("{a: {b: number} c: boolean}") < p("{a: {b: number}}"));
    assert!(p("{a: {b: number}}") > p("{a: {b: number} c: boolean}"));

    assert_eq!(p("{a: {b: boolean} c: boolean}").partial_cmp(&p("{a: {b: number}}")), None);
}

#[test]
fn subtyping_functions() {
    assert!(p("(fn {} -> {})") == p("(fn {} -> {})"));

    assert!(p("(fn {} -> {a: boolean})") < p("(fn {} -> {})"));
    assert!(p("(fn {} -> {})") > p("(fn {} -> {a: boolean})"));

    assert!(p("(fn {} -> boolean)") < p("(fn {a: number} -> boolean)"));
    assert!(p("(fn {a: number} -> boolean)") > p("(fn {} -> boolean)"));

    assert!(p("(fn {a: boolean} -> {})") > p("(fn {} -> {b: number})"));
    assert!(p("(fn {} -> {b: number})") < p("(fn {a: boolean} -> {})"));

    assert!(p("(fn {a: boolean} {a: boolean} -> number)") > p("(fn {} {} -> number)"));
    assert!(p("(fn {} {} -> number)") < p("(fn {a: boolean} {a: boolean} -> number)"));
}

#[test]
fn structs_with_functions() {
    assert!(p("{f: (fn number -> number)}") == p("{f: (fn number -> number)}"));
    assert!(p("{f: (fn boolean -> number)}") != p("{f: (fn number -> number)}"));

    assert!(p("{f: (fn {} -> number)}") < p("{f: (fn {b: boolean} -> number)}"));
    assert!(p("{f: (fn {b: boolean} -> number)}") > p("{f: (fn {} -> number)}"));

    assert!(p("{f: (fn {} -> number) g: (fn {} -> number)}") == p("{f: (fn {} -> number) g: (fn {} -> number)}"));

    assert!(p("{f: (fn {} -> number) g: (fn {} -> number)}") < p("{f: (fn {b: boolean} -> number) g: (fn {} -> number)}"));
    assert!(p("{f: (fn {} -> number) g: (fn {} -> number)}") < p("{f: (fn {} -> number) g: (fn {b: boolean} -> number)}"));
    assert!(p("{f: (fn {} -> number) g: (fn {} -> number)}") < p("{f: (fn {b: boolean} -> number) g: (fn {b: boolean} -> number)}"));
}