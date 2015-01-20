#![allow(unstable)]

extern crate arena;

use arena::TypedArena;

use exp::Exp as E;
use self::MonoTyData as MT;
use symbol::{Symbol, Table, Symbols};
use union_find::{UnionFind, UnionFindable};

use std::borrow::Cow;
use std::cell::Cell;
#[cfg(feature = "debug")] use std::cmp;
use std::collections::HashSet;
use std::fmt;
use std::iter::repeat;
#[cfg(feature = "debug")] use std::num::Int;

pub mod exp;
pub mod symbol;
pub mod union_find;

pub type TyVar<'a> = Symbol<'a>;

pub type A = u8;

#[derive(Clone,Copy,Eq,PartialEq)]
pub struct TyFun<'a> {
    pub name: Symbol<'a>,
    pub arity: A,
}

#[derive(Copy,Clone,PartialEq)]
pub enum MonoTyData<'a, 'b> where 'a: 'b {
    Var(TyVar<'a>),
    App(TyFun<'a>, &'b [MonoTy<'a,'b>]),
}

#[derive(Show)]
pub struct MonoTy<'a,'b> where 'a: 'b {
    uf: UnionFind<'b, MonoTy<'a,'b>>,
    ty: Cell<MonoTyData<'a, 'b>>,
}

impl<'a, 'b> PartialEq for MonoTy<'a, 'b> where 'a: 'b {
    fn eq(&self, other: &Self) -> bool {
        self.ty.get() == other.ty.get()
    }
}

pub enum Ty<'a,'b> where 'a: 'b {
    Quant(Vec<TyVar<'a>>, &'b MonoTy<'a,'b>),
}

pub struct Ctx<'a, 'b> where 'a: 'b {
    symbols: Symbols<'a>,
    assumptions: Table<'b, Ty<'a,'b>>,
    #[cfg(feature = "debug")] indent: u8,
}

pub struct TyVarIter<'a, 'b>(Box<Iterator<Item=TyVar<'a>> + 'b>);

pub type MonoTyCow<'a, 'b> = Cow<'b, MonoTy<'a,'b>, MonoTy<'a,'b>>;

impl<'a, 'b> fmt::String for Ctx<'a, 'b> where 'a: 'b {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.assumptions.fmt(f, &self.symbols)
    }
}

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

impl<'a,'b> MonoTy<'a,'b> where 'a: 'b {
    fn copy(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>) -> MonoTy<'a,'b> {
        match self.ty.get() {
            MT::Var(a) =>
                UnionFindable::copy(self, |:uf| MonoTy { ty: Cell::new(MT::Var(a)), uf: uf }),
            MT::App(d, ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                          .map( |t| t.copy(arena) )
                                                          .collect()))),
                uf: UnionFind::new(),
            },
        }
    }

    pub fn free<'c>(&'c self) -> TyVarIter<'a,'c> {
        match self.ty.get() {
            MT::Var(a) => TyVarIter(Box::new(Some(a).into_iter())),
            MT::App(_, ts) => TyVarIter(Box::new(ts.iter().flat_map( |t| t.free() ))),
        }
    }

    fn subst<'c>(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, substs: &'c Table<'a, &'b MonoTy<'a,'b>>) -> MonoTy<'a,'b> where 'a: 'c, 'b: 'c {
        match self.ty.get() {
            MT::Var(ref a) => substs.look(a).unwrap_or(&self).copy(arena),
            MT::App(d, ref ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                .map( |t| t.subst(arena, substs) )
                                                .collect()))),
                uf: UnionFind::new(),
            },
        }
    }

    pub fn unify(&'b self, other: &'b MonoTy<'a,'b>) -> Result<(), ()> {
        let ta = self.find();
        let tb = other.find();
        //println!("UNIFY: {:?} , {:?}", ta, tb);
        match (ta.ty.get(), tb.ty.get()) {
            (MT::App(da, tsa), MT::App(db, tsb)) if da == db => {
                for (ta,tb) in tsa.iter().zip(tsb.iter()) {
                    try!(ta.unify(tb))
                }
                Ok(())
            },
            (MT::App(_,_), MT::App(_,_)) => Err(()),
            _ => Ok(ta.union(tb)),
        }
    }

    pub fn gen(&'b self, sym_arena: &'b TypedArena<MonoTy<'a,'b>>, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, ctx: &Ctx<'a,'b>) -> Ty<'a,'b> {
        let mut set = self.free().collect::<HashSet<_>>();
        for ref a in ctx.free() {
            set.remove(a);
        }
        Ty::Quant(set.into_iter().collect(), sym_arena.alloc(self.copy(arena)))
    }

}

impl<'a,'b> UnionFindable<'b> for MonoTy<'a,'b> where 'a: 'b {
    fn as_union_find<'c>(&'c self) -> &'c UnionFind<'b, Self> {
        &self.uf
    }

    fn on_union<'c>(&'c self, parent: &'b Self) {
        let x = self.ty.get();
        let p = parent;
        let y = p.ty.get();
        //println!("Child: {:?} {:p}, parent: {:?} {:p}", x, &self.uf as *const _, y, &parent.uf as *const _);
        if let (MT::App(_,_), MT::Var(_)) = (x, y) {
            // Var should never be the child of an App
            self.ty.set(y);
            p.ty.set(x);
        }
    }
}

impl<'a,'b> Ty<'a,'b> where 'a: 'b {
    fn free<'c>(&'c self) -> TyVarIter<'a, 'c> {
        match *self {
            Ty::Quant(ref a, ref t) =>
                TyVarIter(Box::new(t.free().filter( move |&a_| !a.iter().any( |&a| a_ == a )))),
        }
    }

    pub fn inst<'c>(&'c self, sym_arena: &'b TypedArena<MonoTy<'a,'b>>, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, symbols: &'c mut Symbols<'a>) -> Result<MonoTy<'a,'b>,()> {
        match *self {
            Ty::Quant(ref a, ref t) => {
                let mut substs = symbols.empty();
                for a in a.iter() {
                    substs.enter(a, &*sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(try!(symbols.fresh()))), uf: UnionFind::new() }));
                }
                Ok(t.subst(arena, &mut substs))
            }
        }
    }
}

impl<'a,'b> fmt::String for Ty<'a,'b> where 'a: 'b {
    fn fmt<'c,'d>(&'c self, f: &'d mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ty::Quant(ref a, &MonoTy { ref ty, ..}) => {
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

impl<'a,'b> Ctx<'a,'b> where 'a: 'b {
    #[cfg(feature = "debug")]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: Symbols<'a>) -> Ctx<'a,'b> {
        Ctx {
            assumptions: assumptions,
            symbols: symbols,
            indent: 0,
        }
    }

    #[cfg(not(feature = "debug"))]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: Symbols<'a>) -> Ctx<'a,'b> {
        Ctx {
            assumptions: assumptions,
            symbols: symbols,
        }
    }

    pub fn free<'c>(&'c self) -> TyVarIter<'a,'c> {
        TyVarIter(Box::new(self.assumptions.values().flat_map( |s| s.free() )))
    }

    #[cfg(feature = "debug")] fn indent(&mut self, delta: i8) -> u8 {
        let indent = self.indent;
        self.indent = (indent as i8).saturating_add(delta) as u8;
        cmp::max(cmp::min(indent, 80), 0)
    }
    #[cfg(not(feature = "debug"))] #[inline] fn indent(&mut self, _: i8) -> u8 { 0 }

    #[cfg(feature = "debug")] fn debug<T>(t: T) where T: FnOnce() {
        t();
    }

    #[cfg(not(feature = "debug"))] #[inline] fn debug<T>(_: T) where T: FnOnce() {}
}

pub fn hm<'a,'b,'c>(ctx: &'c mut Ctx<'a,'b>,
                    exp: &'b E<'a>,
                    sym_arena: &'b TypedArena<MonoTy<'a,'b>>,
                    arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>
                   ) -> Result<MonoTy<'a,'b>, ()>
    where 'a: 'b
{
    Ctx::debug(|| {
        let indent = ctx.indent(2);
        print!("{}", repeat(' ').take(indent as usize).collect::<String>());
        println!("{} ⊦ {}: ", ctx, exp);
    });
    #[inline]
    fn end<'a,'b>(ctx: &mut Ctx<'a,'b>, res: &MonoTy<'a,'b>) where 'a: 'b {
        Ctx::debug(|| {
            let indent = ctx.indent(-2);
            print!("{}", repeat(' ').take(indent as usize).collect::<String>());
            println!("{:?}", res.find_immutable().ty.get() );
        })
    }
    let res = match *exp {
        E::Var(ref x) => {
            let res = try!(ctx.assumptions.look(x).ok_or(()))
                .inst(sym_arena, arena, &mut ctx.symbols);
            if let Ok(ref res) = res { end(ctx, res) }
            res
        },
        E::App(ref e0, ref e1) => {
            let fun = TyFun { name: try!(ctx.symbols.symbol("→")), arity: 2 };
            let t0 = sym_arena.alloc(try!(hm(ctx, &**e0, sym_arena, arena)));
            let t1 = try!(hm(ctx, &**e1, sym_arena, arena));
            let t = MT::Var(try!(ctx.symbols.fresh()));
            let args = arena.alloc(vec![t1, MonoTy { ty: Cell::new(t), uf: UnionFind::new() }]);
            let app = sym_arena.alloc(MonoTy {
                ty: Cell::new(MT::App(fun, &**args)),
                uf: UnionFind::new(),
            });
            try!(t0.unify(app));
            let res = UnionFindable::copy(&args[1], move |:uf| MonoTy {
                ty: Cell::new(t),
                uf: uf,
            });
            end(ctx, &res);
            Ok(res)
        },
        E::Abs(ref x, ref e) => {
            let fun = TyFun { name: try!(ctx.symbols.symbol("→")), arity: 2 };
            let t = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(try!(ctx.symbols.fresh()))), uf: UnionFind::new() });
            // TODO: Alpha substitution etc.
            let old = ctx.assumptions.enter(x, Ty::Quant(vec![], t));
            let res = try!(hm(ctx, &**e, sym_arena, arena));
            let t = match old {
                Some(v) => ctx.assumptions.enter(x, v),
                None => ctx.assumptions.delete(x)
            }.unwrap();
            let t = match t {
                Ty::Quant(_, t) => t,
            };
            let args = arena.alloc(vec![t.copy(arena), res]);
            let app = MonoTy {
                ty: Cell::new(MT::App(fun, &**args)),
                uf: UnionFind::new(),
            };
            end(ctx, &app);
            Ok(app)
        },
        E::Let(ref x, ref e0, ref e1) => {
            let t = try!(hm(ctx, &**e0, sym_arena, arena));
            let s = sym_arena.alloc(t).gen(sym_arena, arena, ctx);
            // TODO: Alpha substitution etc.
            let old = ctx.assumptions.enter(x, s);
            let res = hm(ctx, &**e1, sym_arena, arena);
            match old {
                Some(v) => ctx.assumptions.enter(x, v),
                None => ctx.assumptions.delete(x)
            };
            res
        }
    };
    res
}

#[test]
fn it_works() {
    let sym_arena = TypedArena::new();
    let arena = TypedArena::new();
    let mut symbols = Symbols::new();
    //let fun = TyFun { name: symbols.symbol("→").unwrap(), arity: 2 };
    /*let set = TyFun { name: symbols.symbol("Set").unwrap(), arity: 1 };
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
    let inst = s.inst(&arena, &mut symbols).unwrap();
    //println!("{:?}", substs.look(&symbols.symbol("α").unwrap()));
    {
        println!("{:?}", inst.ty.get());
        let Ty::Quant(_, ref t) = s;
        println!("{:?}", t.uf);

        //let x = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: UnionFind::new() });
        //let y = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("β").unwrap())), uf: UnionFind::new() });
        let z = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(symbols.symbol("a").unwrap())), uf: UnionFind::new() });

        //let arena = TypedArena::new();
        //let t = t.copy(&arena);
        /*x.union(y);
        z.union(x);
        z.union(t);*/
        z.unify(&inst).unwrap();
        println!("{:?}", z.find().ty.get());
        println!("{:?}", inst.find().ty.get());
        //println!("{:?} {:?} {:?}", x.find() as *const _, y.find() as *const _, z.find() as *const _);
        println!("{:?}", s.free().map( |ref s| symbols.name(s) ).collect::<HashSet<_>>());
    }*/
    let mut assumptions = symbols.empty();
    let int = MT::App(TyFun { name: symbols.symbol("int").unwrap(), arity: 0 }, &[]);
    let boolean = MT::App(TyFun { name: symbols.symbol("bool").unwrap(), arity: 0 }, &[]);
    assumptions.enter(
        &symbols.symbol("n").unwrap(),
        Ty::Quant(vec![],
                  sym_arena.alloc(MonoTy { ty: Cell::new(int), uf: UnionFind::new() })));
    assumptions.enter(
        &symbols.symbol("true").unwrap(),
        Ty::Quant(vec![],
                  sym_arena.alloc(MonoTy { ty: Cell::new(boolean), uf: UnionFind::new() })));
    assumptions.enter(
        &symbols.symbol("false").unwrap(),
        Ty::Quant(vec![],
                  sym_arena.alloc(MonoTy { ty: Cell::new(boolean), uf: UnionFind::new() })));
    //let a = MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: UnionFind::new() };
    /*assumptions.enter(
        &symbols.symbol("id").unwrap(),
        Ty::Quant(vec![symbols.symbol("α").unwrap()],
            MonoTy {
                ty: Cell::new(MT::App(fun, &**arena.alloc(vec![
                    UnionFindable::copy(&a, |uf|
                        MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: uf }),
                    UnionFindable::copy(&a, |uf|
                        MonoTy { ty: Cell::new(MT::Var(symbols.symbol("α").unwrap())), uf: uf })
                ]))),
                uf: UnionFind::new() }));*/
    /*let exp = E::App(
        Box::new(E::Var(symbols.symbol("id").unwrap())),
        Box::new(E::Var(symbols.symbol("n").unwrap())));*/
    let exp = E::Let(symbols.symbol("id").unwrap(),
        Box::new(E::Abs(symbols.symbol("x").unwrap(),
            Box::new(E::Var(symbols.symbol("x").unwrap()))
            /*Box::new(E::App(
                Box::new(E::Var(symbols.symbol("x").unwrap())),
                Box::new(E::Var(symbols.symbol("x").unwrap()))))*/
        )),
        Box::new(E::App(
            Box::new(E::Var(symbols.symbol("id").unwrap())),
            Box::new(E::Var(symbols.symbol("n").unwrap()))),
        ));
    let mut ctx = Ctx::new(assumptions, symbols);
    let ty = hm(&mut ctx, &exp, &sym_arena, &arena).unwrap();
    assert_eq!(int, ty.find().ty.get());

    let exp = E::Let(ctx.symbols.symbol("bar").unwrap(),
        Box::new(E::Abs(ctx.symbols.symbol("x").unwrap(),
            Box::new(E::Let(ctx.symbols.symbol("foo").unwrap(),
                Box::new(E::Abs(ctx.symbols.symbol("y").unwrap(),
                    Box::new(E::Var(ctx.symbols.symbol("x").unwrap())))),
                Box::new(E::Var(ctx.symbols.symbol("foo").unwrap())))))),
        Box::new(E::Var(ctx.symbols.symbol("bar").unwrap())));
    hm(&mut ctx, &exp, &sym_arena, &arena).unwrap();
}
