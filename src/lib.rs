extern crate snoot;
extern crate tendril;

pub mod parse;

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
