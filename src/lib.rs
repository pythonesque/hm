extern crate arena;

use self::MonoTy as MT;

use std::borrow::Cow;
use std::fmt;

use symbol::{Symbol, Table, Symbols};

pub mod symbol;

pub type Var<'a> = Symbol<'a>;

pub type TyVar<'a> = Symbol<'a>;

pub type A = u8;

#[derive(Copy,Clone,Eq,PartialEq)]
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

#[derive(Clone)]
pub enum MonoTy<'a> {
    Var(TyVar<'a>),
    App(TyFun<'a>, Vec<MonoTy<'a>>),
}

pub enum Ty<'a> {
    Quant(Vec<TyVar<'a>>, MonoTy<'a>),
}

pub struct Ctx<'a> {
    assumptions: Table<'a, Ty<'a>>,
}

pub struct Judgment<'a> {
    ctx: Ctx<'a>,
    exp: Exp<'a>,
    ty: Ty<'a>,
}

pub struct TyVarIter<'a, 'b>(Box<Iterator<Item=&'b TyVar<'a>> + 'b>);

pub type MonoTyCow<'a, 'b> = Cow<'b, MonoTy<'a>, MonoTy<'a>>;

impl<'a: 'b, 'b> Iterator for TyVarIter<'a, 'b> {
    type Item = &'b TyVar<'a>;

    fn next(&mut self) -> Option<&'b TyVar<'a>> {
        self.0.next()
    }
}

impl <'a> TyFun<'a> {
    fn infix(&self) -> bool {
        self.arity == 2 && match Symbols::new().name(&self.name) {
            Some("→") => true,
            _ => false,
        }
    }
}

impl<'a> fmt::Show for TyFun<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Symbols::new().fmt(f, &self.name)
    }
}

impl<'a> MonoTy<'a> {
    pub fn free<'b>(&'b self) -> TyVarIter<'a,'b> {
        match *self {
            MT::Var(ref a) => TyVarIter(box Some(a).into_iter()),
            MT::App(_, ref ts) => TyVarIter(box ts.iter().flat_map( |t| t.free() )),
        }
    }

    fn subst<'b>(&'b self, substs: &'b Table<'a, MonoTy<'a>>) -> MonoTyCow<'a,'b> {
        match *self {
            MT::Var(ref a) => Cow::Borrowed(substs.look(a).unwrap_or(self)),
            MT::App(d, ref ts) =>
                Cow::Owned(MT::App(d, ts.iter()
                                        .map( |t| t.subst(substs).into_owned() )
                                        .collect())),
        }
    }
}

impl<'a> fmt::Show for MonoTy<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MT::Var(ref a) => Symbols::new().fmt(f,a),
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

impl<'a> Ty<'a> {
    fn free<'b>(&'b self) -> TyVarIter<'a, 'b> {
        match *self {
            Ty::Quant(ref a, ref t) =>
                TyVarIter(box t.free().filter( move |&a_| !a.iter().any( |&a| *a_ == a ))),
        }
    }

    pub fn inst<'b>(&'b self, symbols: &mut Symbols<'a>) -> Result<MonoTy<'a>,()> {
        match *self {
            Ty::Quant(ref a, ref t) => {
                let mut substs = symbols.empty();
                for a in a.iter() {
                    substs.enter(a, MonoTy::Var(try!(symbols.fresh())));
                }
                Ok(t.subst(&substs).into_owned())
            }
        }
    }
}

impl<'a> fmt::Show for Ty<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ty::Quant(ref a, ref t) => {
                for a in a.iter() {
                    try!(write!(f, "∀ "));
                    try!(Symbols::new().fmt(f, a));
                    try!(write!(f, ". "))
                }
                write!(f, "{}", t)
            },
        }
    }
}

impl<'a> Judgment<'a> {
}

#[test]
fn it_works() {
    use std::collections::HashSet;
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
    let s = Ty::Quant(vec![
        symbols.symbol("β").unwrap(),
        symbols.symbol("α").unwrap(),
    ], t);
    println!("{}", s);
    println!("{}", s.inst(&mut symbols).unwrap());
    println!("{}", s.free().map( |s| symbols.name(s) ).collect::<HashSet<_>>());
}
