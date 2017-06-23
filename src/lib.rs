#[macro_use]
extern crate snoot;
extern crate tendril;

pub mod parse;

use snoot::diagnostic::DiagnosticBag;
use std::cmp::Ordering;
use std::collections::HashMap;

#[derive(Debug)]
pub enum FunctionType {
    Union(Box<FunctionType>, Box<FunctionType>),
    Intersection(Box<FunctionType>, Box<FunctionType>),
    Function {
        arg: Box<Type>,
        ret: Box<Type>,
    }
}

#[derive(Debug)]
pub enum RecordType {
    Union(Box<RecordType>, Box<RecordType>),
    Intersection(Box<RecordType>, Box<RecordType>),
    Record {
        fields: HashMap<String, Type>
    },
}

#[derive(PartialEq, Debug)]
pub enum Type {
    Error {
        diagnostics: DiagnosticBag,
    },
    Function(FunctionType),
    Record(RecordType),
    Boolean,
    Number,
}

fn apply_union<L, R>(l: L, r: R) -> Option<Ordering>
where L: FnOnce() -> Option<Ordering>, R: FnOnce() -> Option<Ordering> {
    use Ordering::*;
    let (l, r) = (l(), r());
    println!("{:?} {:?}", l, r);
    let (l, r) = match (l, r) {
        (None, None) => return None,
        (None, Some(Less)) | (Some(Less), None) => unimplemented!(),
        (None, Some(Greater)) | (Some(Greater), None) => unimplemented!(),
        (None, Some(Equal)) | (Some(Equal), None) => return Some(Greater),
        (Some(l), Some(r)) => (l, r),
    };

    match (l, r) {
        (Equal, Equal) => Some(Equal),
        (Equal, Less) | (Less, Equal) => Some(Greater),
        (Equal, Greater) | (Greater, Equal) => Some(Less),
        (Less, Less) => Some(Greater),
        (Greater, Greater) => Some(Less),
        (Less, Greater) | (Greater, Less) => Some(Greater),
    }
}

impl PartialEq for FunctionType {
    fn eq(&self, other: &FunctionType) -> bool {
        self.partial_cmp(other).map(|a| a == Ordering::Equal).unwrap_or(false)
    }
}

impl PartialOrd for FunctionType {
    fn partial_cmp(&self, other: &FunctionType) -> Option<Ordering> {
        use FunctionType::*;
        match (self, other) {
            (a, &Union(ref left, ref right)) => {
                apply_union(|| a.partial_cmp(left), || a.partial_cmp(right)),
            (a@&Union(_, _), b) => b.partial_cmp(a).map(Ordering::reverse),
            (&Intersection(_, _), _) => unimplemented!(),
            (_, &Intersection(_, _)) => unimplemented!(),
            (&Function{arg: ref a1, ret: ref r1}, &Function{arg: ref a2, ret: ref r2}) => {
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
        }
    }
}


impl PartialEq for RecordType{
    fn eq(&self, other: &RecordType) -> bool {
        self.partial_cmp(other).map(|a| a == Ordering::Equal).unwrap_or(false)
    }
}

impl PartialOrd for RecordType {
    fn partial_cmp(&self, other: &RecordType) -> Option<Ordering> {
        use RecordType::*;
        match (self, other) {
            (a, &Union(ref left, ref right)) =>
                apply_union(|| a.partial_cmp(left), || a.partial_cmp(right)),
            (a@&Union(_, _), b) => b.partial_cmp(a).map(Ordering::reverse),
            (&Intersection(_, _), _) => unimplemented!(),
            (_, &Intersection(_, _)) => unimplemented!(),
            (&RecordType::Record{fields: ref f1}, &RecordType::Record{fields: ref f2}) => {
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
        }
    }
}

impl PartialOrd for Type {
    fn partial_cmp(&self, other: &Type) -> Option<Ordering> {
        match (self, other) {
            (&Type::Number, &Type::Number) => Some(Ordering::Equal),
            (&Type::Boolean, &Type::Boolean) => Some(Ordering::Equal),
            (&Type::Function(ref f1), &Type::Function(ref f2)) => f1.partial_cmp(f2),
            (&Type::Record(ref r1), &Type::Record(ref r2)) => r1.partial_cmp(r2),

            (&Type::Error{..}, _) => None,
            (_, &Type::Error{..}) => None,
            (&Type::Boolean, &Type::Number) => None,
            (&Type::Number, &Type::Boolean) => None,
            (&Type::Number, &Type::Function(_)) => None,
            (&Type::Function(_), &Type::Number) => None,
            (&Type::Boolean, &Type::Function(_)) => None,
            (&Type::Function(_), &Type::Boolean) => None,
            (&Type::Function(_), &Type::Record(_)) => None,
            (&Type::Record(_), &Type::Function(_)) => None,
            (&Type::Boolean, &Type::Record(_)) => None,
            (&Type::Record(_), &Type::Boolean) => None,
            (&Type::Number, &Type::Record(_)) => None,
            (&Type::Record(_), &Type::Number) => None,
        }
    }
}

impl Type {
    fn name(&self) -> &'static str {
        match *self {
            Type::Boolean => "boolean",
            Type::Number => "number",
            Type::Error{..} => "error",
            Type::Function(FunctionType::Function{..}) => "function",
            Type::Function(FunctionType::Union(_, _)) => "function-union",
            Type::Function(FunctionType::Intersection(_, _)) => "function-intersection",
            Type::Record(RecordType::Record{..}) => "record",
            Type::Record(RecordType::Union(_, _)) => "record-union",
            Type::Record(RecordType::Intersection(_, _)) => "record-intersection",
        }
    }

    fn union_with(self, other: Type) -> Type {
        match (self, other) {
            (Type::Function(a), Type::Function(b)) =>
                Type::Function(FunctionType::Union(Box::new(a), Box::new(b))),
            (Type::Record(a), Type::Record(b)) =>
                Type::Record(RecordType::Union(Box::new(a), Box::new(b))),
            (Type::Error{diagnostics: mut diagnostics_a}, Type::Error{diagnostics: diagnostics_b}) => {
                diagnostics_a.append(diagnostics_b);
                Type::Error{ diagnostics: diagnostics_a }
            }
            (error@Type::Error{..}, _) => error,
            (_, error@Type::Error{..}) => error,

            (a, b) => {
                Type::Error {
                    diagnostics: DiagnosticBag::singleton(
                        diagnostic!(&snoot::parse::Span::empty(),
                        "can't union types {} and {}", a.name(), b.name()))
                }
            }
        }
    }
    fn intersect_with(self, other: Type) -> Type {
        match (self, other) {
            (Type::Function(a), Type::Function(b)) =>
                Type::Function(FunctionType::Intersection(Box::new(a), Box::new(b))),
            (Type::Record(a), Type::Record(b)) =>
                Type::Record(RecordType::Intersection(Box::new(a), Box::new(b))),
            (Type::Error{diagnostics: mut diagnostics_a}, Type::Error{diagnostics: diagnostics_b}) => {
                diagnostics_a.append(diagnostics_b);
                Type::Error{ diagnostics: diagnostics_a }
            }
            (error@Type::Error{..}, _) => error,
            (_, error@Type::Error{..}) => error,

            (a, b) => {
                Type::Error {
                    diagnostics: DiagnosticBag::singleton(
                        diagnostic!(&snoot::parse::Span::empty(),
                        "can't intersect types {} and {}", a.name(), b.name()))
                }
            }
        }
    }
}

#[cfg(test)]
fn p(text: &str) -> Type {
    let r = parse::parse(text);
    assert_eq!(r.len(), 1);
    r.into_iter().next().unwrap()
}


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

    assert!(p("{f: (fn {b: boolean} -> number) g: (fn {} -> number)}") > p("{f: (fn {} -> number) g: (fn {} -> number)}"));
    assert!(p("{f: (fn {} -> number) g: (fn {b: boolean} -> number)}") > p("{f: (fn {} -> number) g: (fn {} -> number)}"));
    assert!(p("{f: (fn {b: boolean} -> number) g: (fn {b: boolean} -> number)}") > p("{f: (fn {} -> number) g: (fn {} -> number)}"));
}

#[test]
fn union_records() {
    assert!(p("{}") == p("(union {} {})"));
    assert!(p("{a:boolean}") > p("(union {a:boolean} {b:number})"));
    assert!(p("{a:boolean b:number}") > p("(union {a:boolean} {b:number})"));
    assert!(p("{a:boolean}") < p("(union {a:boolean b: number} {a:boolean c:number})"));
    assert!(p("{a:boolean b:number}") > p("(union {a:boolean} {a:boolean b:number d:boolean})"));
    assert!(p("{a:boolean b:number}") > p("(union {a:boolean b:number d:boolean} {a:boolean})"));
    assert!(p("(union {a:boolean b:number d:boolean} {a:boolean})") < p("{a:boolean b:number}"));
    assert!(p("{a:boolean}") > p("(union {} {a:boolean})"));
    assert!(p("{a:boolean}") < p("(union {a:boolean b:number} {a:boolean})"));
    assert!(p("{a:boolean}") != p("(union {b:number} {c:number})"));
    assert!(p("(union {a:boolean b:number} {a:boolean c:boolean})") > p("{}"));
    assert!(p("(union {a:boolean b:number} {a:boolean c:boolean})") > p("{a:boolean}"));
}

#[test]
fn union_functions() {
    assert!(p("(union {a:boolean b:number} {a:boolean c:boolean})") == p("(union {a:boolean b:number} {a:boolean c:boolean})"));
}
