#![allow(unstable)]

extern crate arena;
extern crate rustc;

use arena::TypedArena;

use exp::Exp as E;
pub use exp::parse::parse;
use self::MonoTyData as MT;
use symbol::{Symbol, Table, Symbols};
use union_find::{UnionFind, UnionFindable};

use std::borrow::Cow;
use std::cell::Cell;
#[cfg(feature = "debug")] use std::cmp;
use std::error::FromError;
use std::fmt;
use std::iter::repeat;
#[cfg(feature = "debug")] use std::num::Int;

pub mod exp;
pub mod symbol;
mod union_find;

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

#[derive(Debug)]
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

// FIXME: Construct a proper error type.
#[allow(missing_copy_implementations)]
pub struct Error;

impl FromError<symbol::Error> for Error {
    fn from_error(_: symbol::Error) -> Self {
        Error
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Inference failure.")
    }
}


pub struct Ctx<'a,'b,'c> where 'a: 'b, 'a: 'c {
    symbols: &'c mut Symbols<'a>,
    assumptions: Table<'b, Ty<'a,'b>>,
    #[cfg(feature = "debug")] indent: u8,
}

pub type MonoTyCow<'a, 'b> = Cow<'b, MonoTy<'a,'b>, MonoTy<'a,'b>>;

impl<'a,'b,'c> fmt::Display for Ctx<'a,'b,'c> where 'a: 'b, 'a: 'c {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.assumptions.fmt(f, self.symbols)
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

impl<'a> fmt::Debug for TyFun<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        Symbols::new().fmt(f, &self.name)
    }
}

impl<'a,'b> fmt::Debug for MonoTyData<'a,'b> where 'a: 'b {
    fn fmt<'c, 'd>(&'c self, f: &'d mut fmt::Formatter) -> fmt::Result {
        match *self {
            MT::Var(ref a) => Symbols::new().fmt(f,a),
            MT::App(ref d, ref ts) => {
                let mut write_space = !d.infix();
                if write_space { try!(write!(f, "{:?}", d)) }
                for t in ts.iter() {
                    let t = &t.find().ty.get();
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
                UnionFindable::copy(self, |uf| MonoTy { ty: Cell::new(MT::Var(a)), uf: uf }),
            MT::App(d, ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                          .map( |t| t.copy(arena) )
                                                          .collect()))),
                uf: UnionFind::new(),
            },
        }
    }

    // Early return if closure (which is a filter) returns true
    fn free<'c, F>(&'b self, f: &'c mut F) -> bool where 'b: 'c, 'a: 'c, F: FnMut(TyVar<'a>) -> bool {
        match self.find().ty.get() {
            MT::Var(a) => f(a),
            MT::App(_, ts) => {
                ts.iter().any( |t| t.free(f) )
            }
        }
    }

    fn subst<'c>(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, substs: &'c Table<'a, &'b MonoTy<'a,'b>>) -> MonoTy<'a,'b> where 'a: 'c, 'b: 'c {
        match self.find().ty.get() {
            MT::Var(ref a) => substs.look(a).unwrap_or(&self).copy(arena),
            MT::App(d, ref ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                .map( |t| t.subst(arena, substs) )
                                                .collect()))),
                uf: UnionFind::new(),
            },
        }
    }

    pub fn unify(&'b self, other: &'b MonoTy<'a,'b>) -> Result<(), Error> {
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
            (MT::App(_,_), MT::App(_,_)) => Err(Error),
            _ => Ok(ta.union(tb)),
        }
    }

    pub fn gen<'c>(&'b self, ctx: &Ctx<'a,'b,'c>, sym_arena: &'b TypedArena<MonoTy<'a,'b>>, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>) -> Ty<'a,'b> {
        //let mut set = self.free().collect::<Vec<_>>();
        let mut set = Vec::new();
        let ty = sym_arena.alloc(self.copy(arena));
        ty.free( &mut |a| {
            // Want TyVars that are part of our type, but free in the context.
            if !ctx.free( &mut move |b| a == b ) {
                // Type is not bound in any context, yay
                set.push(a);
            }
            false // Never short-circuit.
        });
        set.sort();
        set.dedup();
        Ty::Quant(set, ty)
    }
}

impl<'a,'b> UnionFindable<'b> for MonoTy<'a,'b> where 'a: 'b {
    #[inline]
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
    fn free<'c, F>(&'c self, f: &'c mut F) -> bool where F: FnMut(TyVar<'a>) -> bool {
        match *self {
            Ty::Quant(ref a, ref t) => t.free(&mut |a_| {
                // Want TyVars that are free in t but aren't included in our quantifiers.
                if a.iter().any( |&a| a_ == a ) { return true }
                // Now we know that this is the case, so run the function.
                f(a_)
            })
        }
    }

    pub fn inst<'c>(&'c self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, symbols: &'c mut Symbols<'a>) -> Result<MonoTy<'a,'b>,symbol::Error> where 'a: 'b {
        match *self {
            Ty::Quant(ref a, ref t) => {
                let mut substs = symbols.empty();
                let mut vec = Vec::with_capacity(a.len());
                for _ in range(0, a.len()) {
                    vec.push(MonoTy { ty: Cell::new(MT::Var(try!(symbols.fresh()))), uf: UnionFind::new() });
                }
                let mut b = arena.alloc(vec).iter();
                for a in a.iter() {
                    // Unwrap cannot fail here because we iterate in lockstep.
                    substs.enter(a, b.next().unwrap());
                }
                Ok(t.subst(arena, &mut substs))
            }
        }
    }
}

impl<'a,'b> fmt::Display for Ty<'a,'b> where 'a: 'b {
    fn fmt<'c,'d>(&'c self, f: &'d mut fmt::Formatter) -> fmt::Result {
        match *self {
            Ty::Quant(ref a, ref ty) => {
                for a in a.iter() {
                    try!(write!(f, "∀ "));
                    try!(Symbols::new().fmt(f, a));
                    try!(write!(f, ". "))
                }
                write!(f, "{:?}", ty.find().ty.get())
            },
        }
    }
}

impl<'a,'b,'c> Ctx<'a,'b,'c> where 'a: 'b, 'a: 'c {
    #[cfg(feature = "debug")]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: &'c mut Symbols<'a>) -> Ctx<'a,'b,'c> {
        Ctx {
            assumptions: assumptions,
            symbols: symbols,
            indent: 0,
        }
    }

    #[cfg(not(feature = "debug"))]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: &'c mut Symbols<'a>) -> Ctx<'a,'b,'c> {
        Ctx {
            assumptions: assumptions,
            symbols: symbols,
        }
    }

    fn free<F>(&'c self, f: &'c mut F) -> bool where F: FnMut(TyVar<'a>) -> bool {
        self.assumptions.values().any( |s| s.free(f) )
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

pub fn hm<'a,'b,'c,'d>(ctx: &'c mut Ctx<'a,'b,'d>,
                    exp: &E<'a>,
                    sym_arena: &'b TypedArena<MonoTy<'a,'b>>,
                    arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>
                   ) -> Result<MonoTy<'a,'b>, Error>
    where 'a: 'b, 'a: 'c, 'a: 'd,
{
    Ctx::debug(|| {
        let indent = ctx.indent(2);
        print!("{}", repeat(' ').take(indent as usize).collect::<String>());
        println!("{} ⊦ {}: ", &*ctx, exp);
    });
    #[inline]
    fn end<'a,'b,'c,'d>(ctx: &'c mut Ctx<'a,'b,'d>, res: &MonoTy<'a,'b>) where 'a: 'b, 'a: 'c, 'a: 'd {
        Ctx::debug(|| {
            let indent = ctx.indent(-2);
            print!("{}", repeat(' ').take(indent as usize).collect::<String>());
            println!("{:?}", res.find_immutable().ty.get() );
        })
    }
    Ok(match *exp {
        E::Var(ref x) => {
            let res = try!(try!(ctx.assumptions.look(x)
                           .ok_or(Error))
                           .inst(arena, ctx.symbols));
            end(ctx, &res);
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
            let res = UnionFindable::copy(&args[1], move |uf| MonoTy {
                ty: Cell::new(t),
                uf: uf,
            });
            end(ctx, &res);
            res
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
            app
        },
        E::Let(ref x, ref e0, ref e1) => {
            let t = try!(hm(ctx, &**e0, sym_arena, arena));
            let s = sym_arena.alloc(t).gen(ctx, sym_arena, arena);
            // TODO: Alpha substitution etc.
            let old = ctx.assumptions.enter(x, s);
            let res = try!(hm(ctx, &**e1, sym_arena, arena));
            match old {
                Some(v) => ctx.assumptions.enter(x, v),
                None => ctx.assumptions.delete(x)
            };
            ctx.indent(-2);
            res
        }
    })
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::{Ctx, hm, MonoTy, parse, Ty, TyFun};
    use super::MonoTyData as MT;
    use symbol::Symbols;
    use union_find::{UnionFind, UnionFindable};

    use std::cell::Cell;
    use arena::TypedArena;

    fn bench<'a,B,F>(mut b: B, mut symbols: Symbols<'a>, closure: F)
        where F: for<'b,'c> Fn(Ctx<'a,'b,'c>, &'b TypedArena<MonoTy<'a,'b>>, &'b TypedArena<Vec<MonoTy<'a,'b>>>),
              B: FnMut(&mut FnMut())
    {
        let int = TyFun { name: symbols.symbol("int").unwrap(), arity: 0 };
        let boolean = TyFun { name: symbols.symbol("bool").unwrap(), arity: 0 };
        let n = symbols.symbol("n").unwrap();
        let t = symbols.symbol("true").unwrap();
        let f = symbols.symbol("false").unwrap();
        b( &mut || {
            let n_ty = MonoTy { ty: Cell::new(MT::App(int, &[])), uf: UnionFind::new() };
            let t_ty = MonoTy { ty: Cell::new(MT::App(boolean, &[])), uf: UnionFind::new() };
            let f_ty = MonoTy { ty: Cell::new(MT::App(boolean, &[])), uf: UnionFind::new() };
            let assumptions = symbols.empty();
            let mut ctx = Ctx::new(assumptions, &mut symbols);
            let sym_arena: TypedArena<MonoTy> = TypedArena::new();
            let arena: TypedArena<Vec<MonoTy>> = TypedArena::new();
            ctx.assumptions.enter(&n, Ty::Quant(vec![], &n_ty));
            ctx.assumptions.enter(&t, Ty::Quant(vec![], &t_ty));
            ctx.assumptions.enter(&f, Ty::Quant(vec![], &f_ty));
            closure(ctx, &sym_arena, &arena);//, sym_arena, arena)
        });
    }

    static TRIVIAL: &'static str = r"n";

    static BINARY_PRODUCTS: &'static str = r"
let () lambda r r in
let prod lambda e1 lambda e2
    lambda x x e1 e2 in
let left lambda e
    e lambda x lambda y x in
let right lambda e
    e lambda x lambda y y in

let p prod n false in
let x right p in
let q prod false n in
left p
";

    #[test]
    fn it_works() {

        let mut symbols = Symbols::new();
        let int = TyFun { name: symbols.symbol("int").unwrap(), arity: 0 };
        let bool = TyFun { name: symbols.symbol("bool").unwrap(), arity: 0 };
        let exp1 = parse("let id lambda x x in id n", &mut symbols).unwrap();
        let exp2 = parse("
let bar lambda x
    let foo lambda y x
    in foo
in bar", &mut symbols).unwrap();
        let exp3 = parse(BINARY_PRODUCTS, &mut symbols).unwrap();
        bench(|t| t(), symbols, move |mut ctx, sym_arena, arena| {
            let ty = hm(&mut ctx, &exp1, sym_arena, arena).unwrap();
            assert_eq!(MT::App(int, &[]), ty.find_immutable().ty.get());

            hm(&mut ctx, &exp2, sym_arena, arena).unwrap();

            let ty = hm(&mut ctx, &exp3, sym_arena, arena).unwrap();
            assert_eq!(MT::App(bool, &[]), ty.find_immutable().ty.get());
        });
    }

    #[bench]
    fn bench_trivial_hm(b: &mut test::Bencher) {
        let mut symbols = Symbols::new();
        let int = TyFun { name: symbols.symbol("int").unwrap(), arity: 0 };
        let exp = parse(
            TRIVIAL,
            &mut symbols).unwrap();
        bench(|t| b.iter(|| t()), symbols, move |mut ctx, sym_arena, arena| {
            let ty = hm(&mut ctx, &exp, sym_arena, arena).unwrap();
            assert_eq!(MT::App(int, &[]), ty.find_immutable().ty.get());
        });
    }

    #[bench]
    fn bench_binary_products_hm(b: &mut test::Bencher) {
        let mut symbols = Symbols::new();
        let boolean = TyFun { name: symbols.symbol("bool").unwrap(), arity: 0 };
        let exp = parse(
            BINARY_PRODUCTS,
            &mut symbols).unwrap();
        bench(|t| b.iter(|| t()), symbols, move |mut ctx, sym_arena, arena| {
            let ty = hm(&mut ctx, &exp, sym_arena, arena).unwrap();
            assert_eq!(MT::App(boolean, &[]), ty.find_immutable().ty.get());
        });
    }
}
