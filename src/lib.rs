#![feature(associated_types)]

extern crate arena;

use self::MonoTy as MT;
use self::PolyTy as PT;

use std::iter::repeat;
use std::fmt;

use symbol::{Symbol, Symbols};

pub mod symbol;

pub type Var<'a> = Symbol<'a>;

pub type TyVar<'a> = Symbol<'a>;

pub type A = u8;

#[derive(Copy,Eq,PartialEq)]
pub struct TyFun<'a> {
    pub name: Var<'a>,
    pub arity: A,
}

pub enum Exp<'a> {
    Var(Var<'a>),
    Abs(Var<'a>, Box<Exp<'a>>),
    App(Box<Exp<'a>>, Box<Exp<'a>>),
    Let(Var<'a>, Box<Exp<'a>>),
}

pub enum Ty<'a> {
    Mono(MonoTy<'a>),
    Poly(PolyTy<'a>),
}

pub enum MonoTy<'a> {
    Var(TyVar<'a>),
    App(TyFun<'a>, Vec<MonoTy<'a>>),
}

pub enum PolyTy<'a> {
    Mono(MonoTy<'a>),
    Quant(TyVar<'a>, Box<PolyTy<'a>>)
}

pub struct TyIter<'a, 'b>(Box<Iterator<Item=&'b TyVar<'a>> + 'b>);

impl<'a: 'b, 'b> Iterator for TyIter<'a, 'b> {
    type Item = &'b TyVar<'a>;

    fn next(&mut self) -> Option<&'b TyVar<'a>> {
        self.0.next()
    }
}

impl <'a> TyFun<'a> {
    fn infix(&self) -> bool {
        self.arity == 2 && match Symbols::new().name(&self.name) {
            "→" => true,
            _ => false,
        }
    }
}

impl<'a> fmt::Show for TyFun<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Symbols::new().name(&self.name).fmt(f)
    }
}

impl<'a> MonoTy<'a> {
    fn free<'b>(&'b self) -> TyIter<'a,'b> {
        match *self {
            MT::Var(ref a) => TyIter(box Some(a).into_iter()),
            MT::App(_, ref ts) => TyIter(box ts.iter().flat_map( |t| t.free() )),
        }
    }
}

impl<'a> fmt::Show for MonoTy<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MT::Var(ref a) => Symbols::new().name(a).fmt(f),
            MT::App(ref d, ref ts) => {
                let mut write_space = !d.infix();
                if write_space { try!(write!(f, "{}", d)) }
                for t in ts.iter() {
                    if write_space { try!(write!(f, " ")) }
                    try!(match *t {
                        MT::Var(_) | MT::App(TyFun { arity: 0, .. }, _) => write!(f, "{}", t),
                        _ => write!(f, "({})", t),
                    });
                    if !write_space {
                        try!(write!(f, " {}", d));
                        write_space = true;
                    }
                }
                Ok(())
            }
        }
    }
}

impl<'a> PolyTy<'a> {
    fn free<'b>(&'b self) -> TyIter<'a, 'b> {
        match *self {
            PT::Quant(ref a, ref s) => TyIter(box s.free()
                .zip(repeat(a.clone()))
                .filter_map( |(a_, a)| if *a_ != a { Some(a_) } else { None } )),
            PT::Mono(ref t) => t.free(),
        }
    }
}

impl<'a> fmt::Show for PolyTy<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            PT::Quant(ref a, ref s) => write!(f, "∀ {}. {}", Symbols::new().name(a), s),
            PT::Mono(ref t) => t.fmt(f),
        }
    }
}

impl<'a> Ty<'a> {
    fn free<'b>(&'b self) -> TyIter<'a,'b> {
        match *self {
            Ty::Mono(ref t) => t.free(),
            Ty::Poly(ref s) => s.free(),
        }
    }
}

impl<'a> fmt::Show for Ty<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ty::Mono(ref t) => t.fmt(f),
            Ty::Poly(ref s) => s.fmt(f),
        }
    }
}

#[test]
fn it_works() {
    let mut symbols = Symbols::new();
    let fun = TyFun { name: symbols.symbol("→").unwrap(), arity: 2 };
    let set = TyFun { name: symbols.symbol("Set").unwrap(), arity: 1 };
    let t = MT::App(fun, vec![
        MT::Var(symbols.symbol("α").unwrap()),
        MT::App(set, vec![
            MT::App(fun, vec![
                MT::Var(symbols.symbol("β").unwrap()),
                MT::Var(symbols.symbol("α").unwrap()),
            ]),
        ]),
    ]);
    let s = PT::Quant(symbols.symbol("β").unwrap(), box PT::Mono(t));
    let s = Ty::Poly(PT::Quant(symbols.symbol("α").unwrap(), box s));
    println!("{}", s);
    println!("{}", s.free().collect::<Vec<_>>());
}
