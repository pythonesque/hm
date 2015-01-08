extern crate arena;

use self::MonoTy as MT;

use std::borrow::{Cow, ToOwned};
use std::fmt;

use symbol::{Symbol, Table, Symbols};
use union_find::UnionFind;

pub mod symbol;
pub mod union_find;

pub type Var<'a> = Symbol<'a>;

pub type TyVar<'a> = Symbol<'a>;

pub type A = u8;

#[derive(Clone,Copy,Eq,PartialEq)]
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

pub enum MonoTy<'a,'b> {
    Var(TyVar<'a>, UnionFind<'b>),
    App(TyFun<'a>, Vec<MonoTy<'a,'b>>, UnionFind<'b>),
}

pub enum Ty<'a,'b> {
    Quant(Vec<TyVar<'a>>, MonoTy<'a,'b>),
}

pub struct Ctx<'a> {
    assumptions: Table<'a, Ty<'a,'a>>,
}

pub struct Judgment<'a> {
    ctx: Ctx<'a>,
    exp: Exp<'a>,
    ty: Ty<'a,'a>,
}

pub struct TyVarIter<'a, 'b>(Box<Iterator<Item=&'b TyVar<'a>> + 'b>);

pub type MonoTyCow<'a, 'b> = Cow<'b, MonoTy<'a,'b>, MonoTy<'a,'b>>;

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

impl<'a,'b> MonoTy<'a,'b> {
    fn copy(&'b self) -> MonoTy<'a,'b> {
        match *self {
            MT::Var(a, ref uf) => MT::Var(a, uf.copy()),
            MT::App(d, ref ts, ref uf) => MT::App(d, ts.iter()
                                                       .map( |t| t.copy() )
                                                       .collect(), uf.copy()),
        }
    }

    pub fn free<'c>(&'c self) -> TyVarIter<'a,'c> {
        match *self {
            MT::Var(ref a, ref uf) => TyVarIter(box Some(a).into_iter()),
            MT::App(_, ref ts, ref uf) => TyVarIter(box ts.iter().flat_map( |t| t.free() )),
        }
    }

    fn subst(&'b self, substs: &'b Table<'a, MonoTy<'a,'b>>) -> MonoTy<'a,'b> {
        match *self {
            MT::Var(ref a, ref uf) => substs.look(a).unwrap_or(self).copy(),
            MT::App(d, ref ts, ref uf) =>
                MT::App(d, ts.iter()
                                        .map( |t| t.subst(substs) )
                                        .collect(), uf.copy()),
        }
    }
}

impl<'a,'b> fmt::Show for MonoTy<'a,'b> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            MT::Var(ref a, ref uf) => Symbols::new().fmt(f,a),
            MT::App(ref d, ref ts, ref uf) => {
                let mut write_space = !d.infix();
                if write_space { try!(write!(f, "{}", d)) }
                for t in ts.iter() {
                    if write_space { try!(write!(f, " ")) }
                    try!(match *t {
                        MT::Var(_, _) | MT::App(TyFun { arity: 0, .. }, _, _) =>
                            write!(f, "{}", t),
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

impl<'a,'b> Ty<'a,'b> {
    fn free<'c>(&'c self) -> TyVarIter<'a, 'c> {
        match *self {
            Ty::Quant(ref a, ref t) =>
                TyVarIter(box t.free().filter( move |&a_| !a.iter().any( |&a| *a_ == a ))),
        }
    }

    pub fn inst<'c>(&'b self, substs: &'b mut Table<'b, MonoTy<'a,'b>>, symbols: &'c mut Symbols<'a>) -> Result<MonoTy<'a,'b>,()> {
        match *self {
            Ty::Quant(ref a, ref t) => {
                for a in a.iter() {
                    substs.enter(a, MonoTy::Var(try!(symbols.fresh()), UnionFind::new()));
                }
                Ok(t.subst(substs))
            }
        }
    }
}

impl<'a,'b> fmt::Show for Ty<'a,'b> {
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
    //let sets = UnionFind::new();
}

#[test]
fn it_works() {
    use std::collections::HashSet;
    let mut symbols = Symbols::new();
    let fun = TyFun { name: symbols.symbol("→").unwrap(), arity: 2 };
    let set = TyFun { name: symbols.symbol("Set").unwrap(), arity: 1 };
    let t = MT::App(fun, vec![
        MT::Var(symbols.symbol("α").unwrap(),UnionFind::new()),
        MT::App(set, vec![
            MT::App(fun, vec![
                MT::Var(symbols.symbol("β").unwrap(), UnionFind::new()),
                MT::Var(symbols.symbol("α").unwrap(), UnionFind::new()),
            ], UnionFind::new()),
        ], UnionFind::new()),
    ], UnionFind::new());
    let s = Ty::Quant(vec![
        symbols.symbol("β").unwrap(),
        symbols.symbol("α").unwrap(),
    ], t);
    println!("{}", s);
    let mut substs = symbols.empty();
    println!("{}", s.inst(&mut substs, &mut symbols).unwrap());
    println!("{}", s.free().map( |s| symbols.name(s) ).collect::<HashSet<_>>());
}
