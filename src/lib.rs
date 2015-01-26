#![allow(unstable)]

extern crate arena;
//extern crate collect;
extern crate rustc;

use exp::Exp as E;
pub use exp::parse::parse;
use symbol::{Symbol, Symbols, Table};
use ty::{MonoTy, Ty, TyFun, TyVar};
use ty::MonoTyData as MT;
use union_find::{UnionFind, UnionFindable};

use arena::TypedArena;
//use collect::LruCache;
use std::cell::Cell;
#[cfg(feature = "debug")] use std::cmp;
use std::error::FromError;
use std::fmt;
use std::iter::repeat;
#[cfg(feature = "debug")] use std::num::Int;

pub mod exp;
pub mod symbol;
pub mod ty;
mod union_find;

//const CACHE_CAPACITY: usize = 8;

// FIXME: Construct a proper error type.
pub enum Error {
    Ty(ty::Error),
    Symbol(symbol::Error),
}

pub struct Ctx<'a,'b,'c> where 'a: 'b + 'c {
    symbols: &'c mut Symbols<'a>,
    //tys: Vec<Ty<'a,'b>>,
    //cache: LruCache<Symbol<'a>, usize>,
    //assumptions: Table<'b, usize>,
    assumptions: Table<'b, Ty<'a,'b>>,
    fun: TyFun<'a>,
    #[cfg(feature = "debug")] indent: u8,
}

impl FromError<symbol::Error> for Error {
    fn from_error(e: symbol::Error) -> Self {
        Error::Symbol(e)
    }
}

impl FromError<ty::Error> for Error {
    fn from_error(e: ty::Error) -> Self {
        Error::Ty(e)
    }
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            Error::Ty(ref e) => write!(f, "Type error during inference - {}", e),
            Error::Symbol(ref e) => write!(f, "Symbol error during inference - {}", e),
        }
    }
}

impl<'a,'b,'c> fmt::Display for Ctx<'a,'b,'c> where 'a: 'b + 'c {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        self.assumptions.fmt(f, self.symbols)
    }
}

impl<'a,'b,'c> Ctx<'a,'b,'c> where 'a: 'b + 'c {
    #[cfg(feature = "debug")]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: &'c mut Symbols<'a>) -> Result<Ctx<'a,'b,'c>,symbol::Error> {
        let fun = TyFun { name: try!(symbols.symbol("→")), arity: 2 };
        Ok(Ctx {
            assumptions: assumptions,
            //cache: LruCache::new(),
            //tys: Vec::new(),
            symbols: symbols,
            fun: fun,
            indent: 0,
        })
    }

    #[cfg(not(feature = "debug"))]
    pub fn new(assumptions: Table<'b, Ty<'a,'b>>, symbols: &'c mut Symbols<'a>) -> Result<Ctx<'a,'b,'c>,symbol::Error> where 'a: 'b {
        let fun = TyFun { name: try!(symbols.symbol("→")), arity: 2 };
        Ok(Ctx {
            assumptions: assumptions,
            //cache: LruCache::new(CACHE_CAPACITY),
            //tys: Vec::new(),
            symbols: symbols,
            fun: fun,
        })
    }

    fn free<F>(&'c self, f: &'c mut F) -> bool where F: FnMut(TyVar<'a>) -> bool {
        for s in self.assumptions.values() {
            //let s = &self.tys[*s];
            if s.free(f) { return true }
        }
        false
    }

    #[cfg(feature = "debug")] fn indent<'d>(&'d mut self, delta: i8) -> u8 {
        let indent = self.indent;
        self.indent = (indent as i8).saturating_add(delta) as u8;
        cmp::max(cmp::min(indent, 80), 0)
    }
    #[cfg(not(feature = "debug"))] #[inline] fn indent<'d>(&'d mut self, _: i8) -> u8 { 0 }

    #[cfg(feature = "debug")] fn debug<T>(t: T) where T: FnOnce() {
        t();
    }

    #[cfg(not(feature = "debug"))] #[inline] fn debug<T>(_: T) where T: FnOnce() {}
}

fn gen<'a,'b,'c,'d>(t: &'b MonoTy<'a,'b>, ctx: &'d Ctx<'a,'b,'c>) -> Ty<'a,'b> where 'a: 'b + 'c + 'd {
    let mut set = Vec::new();
    t.free( &mut |a| {
        set.push(a);
        false
    } );
    ctx.free( &mut |b| {
        let mut i = 0;
        while i < set.len() {
            if set[i] == b {
                set.swap_remove(i);
            }
            i += 1;
        }
        false
    } );
    set.sort();
    set.dedup();
    Ty::Quant(set, t)
}

fn inst<'a,'b,'c>(s: &'c Ty<'a,'b>, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, symbols: &'c mut Symbols<'a>) -> Result<MonoTy<'a,'b>,symbol::Error> where 'a: 'b {
    match *s {
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

pub fn hm<'a,'b,'c,'d,'e>(ctx: &'c mut Ctx<'a,'b,'d>,
                    exp: &'e E<'a>,
                    sym_arena: &'b TypedArena<MonoTy<'a,'b>>,
                    arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>
                   ) -> Result<MonoTy<'a,'b>, Error>
    where 'a: 'b + 'c + 'd + 'e, 'a: 'b
{
    Ctx::debug(|| {
        let indent = ctx.indent(2);
        print!("{}", repeat(' ').take(indent as usize).collect::<String>());
        println!("{} ⊦ {}: ", &*ctx, exp);
    });
    #[inline]
    fn end<'a,'b,'c,'d>(ctx: &'c mut Ctx<'a,'b,'d>, res: &MonoTy<'a,'b>) where 'a: 'b + 'c + 'd {
        Ctx::debug(|| {
            let indent = ctx.indent(-2);
            print!("{}", repeat(' ').take(indent as usize).collect::<String>());
            println!("{:?}", res.find_immutable().ty.get() );
        })
    }
    Ok(match *exp {
        E::Var(ref x) => {
            // let res = {
            //     let Ctx { ref mut symbols, ref tys, ref mut cache, ref assumptions, .. } = *ctx;
            //     let i = cache.get(x);
            //     try!(tys[*try!(i.map_or_else( || assumptions.look(x).ok_or(Error), |x| Ok(x) ))]
            //                    .inst(arena, *symbols))
            // };
            let res = match ctx.assumptions.look(x) {
                Some(s) => try!(inst(s, arena, ctx.symbols)),
                None => MonoTy {
                    ty: Cell::new(MT::Var(*x)),
                    uf: UnionFind::new(),
                }
            };
            end(ctx, &res);
            res
        },
        E::App(ref e0, ref e1) => {
            let t0 = sym_arena.alloc(try!(hm(ctx, &**e0, sym_arena, arena)));
            let t1 = try!(hm(ctx, &**e1, sym_arena, arena));
            let t = MT::Var(try!(ctx.symbols.fresh()));
            let args = arena.alloc(vec![t1, MonoTy { ty: Cell::new(t), uf: UnionFind::new() }]);
            let app = sym_arena.alloc(MonoTy {
                ty: Cell::new(MT::App(ctx.fun, &**args)),
                uf: UnionFind::new(),
            });
            try!(t0.unify(app));
            let res = UnionFindable::copy(&args[1], move |:uf| MonoTy {
                ty: Cell::new(t),
                uf: uf,
            });
            end(ctx, &res);
            res
        },
        E::Abs(ref x, ref e) => {
            let t = sym_arena.alloc(MonoTy { ty: Cell::new(MT::Var(try!(ctx.symbols.fresh()))), uf: UnionFind::new() });
            // TODO: Alpha substitution etc.
            //let old = ctx.assumptions.enter(x, ctx.tys.len());
            //ctx.cache.insert(*x, ctx.tys.len());
            //ctx.tys.push(Ty::Quant(vec![], t));
            let old = ctx.assumptions.enter(x, Ty::Quant(vec![], t));
            let res = try!(hm(ctx, &**e, sym_arena, arena));
            let t = match old {
                Some(v) => ctx.assumptions.enter(x, v),
                None => ctx.assumptions.delete(x)
            }.unwrap();
            //ctx.cache.remove(x);
            //let t = ctx.tys.pop().unwrap(); // NOTE: I think this is correct, but it is very fragile.
            let t = match t {
                Ty::Quant(_, t) => t,
            };
            let args = arena.alloc(vec![t.copy(arena), res]);
            let app = MonoTy {
                ty: Cell::new(MT::App(ctx.fun, &**args)),
                uf: UnionFind::new(),
            };
            end(ctx, &app);
            app
        },
        E::Let(ref x, ref e0, ref e1) => {
            let t = try!(hm(ctx, &**e0, sym_arena, arena));
            let s = gen(sym_arena.alloc(t), ctx);
            // TODO: Alpha substitution etc.
            //let old = ctx.assumptions.enter(x, ctx.tys.len());
            //ctx.cache.insert(*x, ctx.tys.len());
            //ctx.tys.push(s);
            let old = ctx.assumptions.enter(x, s);
            let res = try!(hm(ctx, &**e1, sym_arena, arena));
            match old {
                Some(v) => ctx.assumptions.enter(x, v),
                None => ctx.assumptions.delete(x)
            };
            //ctx.cache.remove(x);
            //ctx.tys.pop(); // NOTE: I think this is correct, but it is very fragile.
            ctx.indent(-2);
            res
        }
    })
}

#[cfg(test)]
mod tests {
    extern crate test;

    use super::{Ctx, hm, parse};
    use symbol::Symbols;
    use ty::{MonoTy, Ty, TyFun};
    use ty::MonoTyData as MT;
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
            let mut ctx = Ctx::new(assumptions, &mut symbols).unwrap();
            let sym_arena: TypedArena<MonoTy> = TypedArena::new();
            let arena: TypedArena<Vec<MonoTy>> = TypedArena::new();
            //ctx.tys.push(Ty::Quant(vec![], &n_ty));
            //ctx.assumptions.enter(&n, 0);
            ctx.assumptions.enter(&n, Ty::Quant(vec![], &n_ty));
            //ctx.tys.push(Ty::Quant(vec![], &t_ty));
            //ctx.assumptions.enter(&t, 1);
            ctx.assumptions.enter(&t, Ty::Quant(vec![], &t_ty));
            //ctx.tys.push(Ty::Quant(vec![], &f_ty));
            //ctx.assumptions.enter(&f, 2);
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
right p
";

    static BINARY_SUMS: &'static str = r"
let void r in
let abort lambda e e in
let Left lambda e
    lambda x lambda y x e in
let Right lambda e
    lambda x lambda y y e in
let case lambda e lambda l lambda r
    e l r in

let f lambda f
    let s Right true in
    let t Left n in
    let _ f s in
    let _ f t in
    let l lambda x1 false in
    let r lambda x2 x2 in
    case s l r
in f lambda x lambda y y
";

    static OCCURS_CHECK: &'static str = r"
let foo lambda x x x in
foo
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
        let exp4 = parse(BINARY_SUMS, &mut symbols).unwrap();
        let exp5 = parse(OCCURS_CHECK, &mut symbols).unwrap();
        bench(|t| t(), symbols, move |mut ctx, sym_arena, arena| {
            let ty = hm(&mut ctx, &exp1, sym_arena, arena).unwrap();
            assert_eq!(MT::App(int, &[]), ty.find_immutable().ty.get());

            hm(&mut ctx, &exp2, sym_arena, arena).unwrap();

            let ty = hm(&mut ctx, &exp3, sym_arena, arena).unwrap();
            assert_eq!(MT::App(bool, &[]), ty.find_immutable().ty.get());

            let ty = hm(&mut ctx, &exp4, sym_arena, arena).unwrap();
            assert_eq!(MT::App(bool, &[]), ty.find_immutable().ty.get());

            hm(&mut ctx, &exp5, sym_arena, arena).err().expect("Occurs check failed");
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

    #[bench]
    fn bench_binary_sums_hm(b: &mut test::Bencher) {
        let mut symbols = Symbols::new();
        let boolean = TyFun { name: symbols.symbol("bool").unwrap(), arity: 0 };
        let exp = parse(
            BINARY_SUMS,
            &mut symbols).unwrap();
        bench(|t| b.iter(|| t()), symbols, move |mut ctx, sym_arena, arena| {
            let ty = hm(&mut ctx, &exp, sym_arena, arena).unwrap();
            assert_eq!(MT::App(boolean, &[]), ty.find_immutable().ty.get());
        });
    }
}
