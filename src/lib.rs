#![allow(unstable)]

extern crate arena;

use arena::TypedArena;

use self::MonoTyData as MT;

use std::borrow::Cow;
use std::cell::Cell;
use std::fmt;

use symbol::{Symbol, Table, Symbols};
use union_find::{UnionFind, UnionFindable};

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

#[derive(Copy,Clone)]
pub enum MonoTyData<'a, 'b> where 'a: 'b {
    Var(TyVar<'a>),
    App(TyFun<'a>, &'b [MonoTy<'a,'b>]),
}

#[derive(Show)]
pub struct MonoTy<'a,'b> where 'a: 'b {
    uf: UnionFind<'b, MonoTy<'a,'b>>,
    ty: Cell<MonoTyData<'a, 'b>>,
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

pub struct TyVarIter<'a, 'b>(Box<Iterator<Item=TyVar<'a>> + 'b>);

pub type MonoTyCow<'a, 'b> = Cow<'b, MonoTy<'a,'b>, MonoTy<'a,'b>>;

impl<'a: 'b, 'b> Iterator for TyVarIter<'a, 'b> {
    type Item = TyVar<'a>;

    fn next(&mut self) -> Option<TyVar<'a>> {
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

impl<'a,'b> fmt::Show for MonoTyData<'a,'b> where 'a: 'b {
    fn fmt<'c, 'd>(&'c self, f: &'d mut fmt::Formatter) -> fmt::Result {
        match *self {
            MT::Var(ref a) => Symbols::new().fmt(f,a),
            MT::App(ref d, ref ts) => {
                let mut write_space = !d.infix();
                if write_space { try!(write!(f, "{:?}", d)) }
                for t in ts.iter() {
                    let t = &t.ty.get();
                    if write_space { try!(write!(f, " ")) }
                    try!(match *t {
                        MT::Var(_) | MT::App(TyFun { arity: 0, .. }, _) =>
                            write!(f, "{:?}", t),
                        _ => write!(f, "({:?})", t),
                    });
                    if !write_space {
                        try!(write!(f, " {:?}", d));
                        write_space = true;
                    }
                }
                Ok(())
            }
        }
    }
}

impl<'a,'b> MonoTy<'a,'b> {
    fn copy(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>) -> MonoTy<'a,'b> {
        MonoTy {
            ty: Cell::new(match self.ty.get() {
                MT::Var(a) => MT::Var(a),
                MT::App(d, ts) => MT::App(d, &**arena.alloc(ts.iter()
                                                                  .map( |t| t.copy(arena) )
                                                                  .collect()))
            }),
            uf: UnionFind::new(),//self.copy_union_find(),
        }
    }

    pub fn free<'c: 'b>(&'c self) -> TyVarIter<'a,'c> {
        match self.ty.get() {
            MT::Var(a) => TyVarIter(Box::new(Some(a).into_iter())),
            MT::App(_, ts) => TyVarIter(Box::new(ts.iter().flat_map( |t| t.free() ))),
        }
    }

    fn subst(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, substs: &'b Table<'a, MonoTy<'a,'b>>) -> MonoTy<'a,'b> {
        match self.ty.get() {
            MT::Var(ref a) => substs.look(a).unwrap_or(self).copy(arena),
            MT::App(d, ref ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                .map( |t| t.subst(arena, substs) )
                                                .collect()))),
                uf: UnionFind::new(),//self.copy_union_find(),
            },
        }
    }

    pub fn unify(&'b self, other: &'b MonoTy<'a,'b>) -> Result<(), ()> {
        let ta = self.find();
        let tb = other.find();
        match (ta.ty.get(), tb.ty.get()) {
            (MT::App(da, tsa), MT::App(db, tsb)) if da == db =>
                tsa.iter().zip(tsb.iter()).fold(Ok(()), |_, (ta,tb)| ta.unify(tb) ),
            (MT::App(_,_), MT::App(_,_)) => Err(()),
            _ => Ok(ta.union(tb)),
        }
    }
}

impl<'a,'b> UnionFindable<'b> for MonoTy<'a,'b> {
    fn as_union_find<'c>(&'c self) -> &'c UnionFind<'b, Self> {
        &self.uf
    }

    fn on_union(&'b self, parent: &'b Self) {
        let x = self.ty.get();
        let y = parent.ty.get();
        if let (MT::App(_,_), MT::Var(_)) = (x, y) {
            // Var should never be the child of an App
            self.ty.set(y);
            parent.ty.set(x);
        }
    }
}

impl<'a,'b> Ty<'a,'b> {
    fn free<'c: 'b>(&'c self) -> TyVarIter<'a, 'c> {
        match *self {
            Ty::Quant(ref a, ref t) =>
                TyVarIter(Box::new(t.free().filter( move |&a_| !a.iter().any( |&a| a_ == a )))),
        }
    }

    pub fn inst<'c>(&'b self, substs: &'b mut Table<'b, MonoTy<'a,'b>>, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, symbols: &'c mut Symbols<'a>) -> Result<MonoTy<'a,'b>,()> {
        match *self {
            Ty::Quant(ref a, ref t) => {
                for a in a.iter() {
                    substs.enter(a, MonoTy { ty: Cell::new(MT::Var(try!(symbols.fresh()))), uf: UnionFind::new() });
                }
                Ok(t.subst(arena, substs))
            }
        }
    }
}

impl<'a,'b> fmt::Show for Ty<'a,'b> where 'a: 'b {
    fn fmt<'c,'d>(&'c self, f: &'d mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ty::Quant(ref a, MonoTy { ref ty, ..}) => {
                for a in a.iter() {
                    try!(write!(f, "∀ "));
                    try!(Symbols::new().fmt(f, a));
                    try!(write!(f, ". "))
                }
                write!(f, "{:?}", ty.get())
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
    let sym_arena = TypedArena::new();
    let arena = TypedArena::new();
    let mut symbols = Symbols::new();
    let fun = TyFun { name: symbols.symbol("→").unwrap(), arity: 2 };
    let set = TyFun { name: symbols.symbol("Set").unwrap(), arity: 1 };
    let t = MonoTy { ty: Cell::new(MT::App(fun, &**arena.alloc(vec![
        MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: UnionFind::new() },
        MonoTy { ty: Cell::new(MT::App(set, &**arena.alloc(vec![
            MonoTy { ty: Cell::new(MT::App(fun, &**arena.alloc(vec![
                MonoTy { ty: Cell::new(MT::Var(symbols.symbol("β").unwrap())), uf: UnionFind::new() },
                MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: UnionFind::new() },
            ]))), uf: UnionFind::new() },
        ]))), uf: UnionFind::new() },
    ]))), uf: UnionFind::new() };
    let s = Ty::Quant(vec![
        symbols.symbol("β").unwrap(),
        symbols.symbol("α").unwrap(),
    ], t);
    println!("{:?}", s);
    let mut substs = symbols.empty();
    let inst = s.inst(&mut substs, &arena, &mut symbols).unwrap();
    println!("{:?}", inst.ty.get());
    //println!("{:?}", substs.look(&symbols.symbol("α").unwrap()));
    {
        let Ty::Quant(_, ref t) = s;
        println!("{:?}", t.uf);

        let x = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: UnionFind::new() });
        let y = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("β").unwrap())), uf: UnionFind::new() });
        let z = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("a").unwrap())), uf: UnionFind::new() });

        //let arena = TypedArena::new();
        //let t = t.copy(&arena);
        /*x.union(y);
        z.union(x);
        z.union(t);*/
        z.unify(&inst);
        println!("{:?}", z.find().ty.get());
        println!("{:?}", inst.find().ty.get());
        //println!("{:?} {:?} {:?}", x.find() as *const _, y.find() as *const _, z.find() as *const _);
        println!("{:?}", s.free().map( |ref s| symbols.name(s) ).collect::<HashSet<_>>());
    }
}
