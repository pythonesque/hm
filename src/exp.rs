use self::Exp as E;
use symbol::{Symbol, Symbols};

use std::fmt;

pub type Var<'a> = Symbol<'a>;

pub enum Exp<'a> {
    Var(Var<'a>),
    Abs(Var<'a>, Box<Exp<'a>>),
    App(Box<Exp<'a>>, Box<Exp<'a>>),
    Let(Var<'a>, Box<Exp<'a>>, Box<Exp<'a>>),
}

impl<'a> fmt::String for Exp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            E::Var(ref x) => Symbols::new().fmt(f, x),
            E::Abs(ref x, ref e) => {
                try!(write!(f, "λ"));
                try!(Symbols::new().fmt(f, x));
                write!(f, ". {}", e)
            },
            E::App(ref e1, ref e2) => {
                write!(f, "{} {}", e1, e2)
            },
            E::Let(ref x, ref e1, ref e2) => {
                try!(write!(f, "let "));
                try!(Symbols::new().fmt(f, x));
                write!(f, " = {} in {}", e1, e2)
            },
        }
    }
}

