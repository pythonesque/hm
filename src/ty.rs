use arena::TypedArena;

use self::MonoTyData as MT;
use std::cell::Cell;
use std::fmt;
use symbol::{Symbol, Symbols, Table};
use union_find::{self, UnionFind, UnionFindable};

pub type TyVar<'a> = Symbol<'a>;

pub type Arity = u8;

// FIXME: Create a proper error type.
#[allow(missing_copy_implementations)]
#[derive(Debug)]
pub struct Error;

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "Unification failed.")
    }
}

#[derive(Clone,Copy,Eq,PartialEq)]
pub struct TyFun<'a> {
    pub name: Symbol<'a>,
    pub arity: Arity,
}

#[derive(Copy,Clone,PartialEq)]
pub enum MonoTyData<'a, 'b> where 'a: 'b {
    Var(TyVar<'a>),
    App(TyFun<'a>, &'b [MonoTy<'a,'b>]),
}

#[derive(Debug)]
pub struct MonoTy<'a,'b> where 'a: 'b {
    pub uf: UnionFind<'b, MonoTy<'a,'b>>,
    pub ty: Cell<MonoTyData<'a, 'b>>,
}

impl<'a, 'b> PartialEq for MonoTy<'a, 'b> where 'a: 'b {
    fn eq(&self, other: &Self) -> bool {
        self.ty.get() == other.ty.get()
    }
}

pub enum Ty<'a,'b> where 'a: 'b {
    Quant(Vec<TyVar<'a>>, &'b MonoTy<'a,'b>),
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
                    let t = &union_find::find(t).ty.get();
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
    pub fn copy(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>) -> MonoTy<'a,'b> {
        match self.ty.get() {
            MT::Var(a) =>
                union_find::copy(self, |uf| MonoTy { ty: Cell::new(MT::Var(a)), uf: uf }),
            MT::App(d, ts) => MonoTy {
                ty: Cell::new(MT::App(d, &**arena.alloc(ts.iter()
                                                          .map( |t| t.copy(arena) )
                                                          .collect()))),
                uf: UnionFind::new(),
            },
        }
    }

    // Early return if closure (which is a filter) returns true
    pub fn free<'c, F>(&'b self, f: &'c mut F) -> bool where 'b: 'c, 'a: 'c, F: FnMut(TyVar<'a>) -> bool {
        match union_find::find(self).ty.get() {
            MT::Var(a) => f(a),
            MT::App(_, ts) => {
                ts.iter().any( |t| t.free(f) )
            }
        }
    }

    pub fn subst<'c>(&'b self, arena: &'b TypedArena<Vec<MonoTy<'a,'b>>>, substs: &'c Table<'a, &'b MonoTy<'a,'b>>) -> MonoTy<'a,'b> {
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

    pub fn unify(&'b self, other: &'b MonoTy<'a,'b>) -> Result<(), Error> {
        let ta = union_find::find(self);
        let tb = union_find::find(other);
        //println!("UNIFY: {:?} , {:?}", ta, tb);
        match (ta.ty.get(), tb.ty.get()) {
            (MT::App(da, tsa), MT::App(db, tsb)) if da == db => {
                for (ta,tb) in tsa.iter().zip(tsb.iter()) {
                    try!(ta.unify(tb))
                }
                Ok(())
            },
            (MT::App(_,_), MT::App(_,_)) => Err(Error),
            (MT::App(_,ts), MT::Var(t)) | (MT::Var(t), MT::App(_, ts)) => {
                // Occurs check
                if ts.iter().any( |t_| t_.free( &mut |t_| t_ == t ) ) { return Err(Error) }
                Ok(union_find::union(ta, tb))
            },
            _ => Ok(union_find::union(ta, tb)),
        }
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
    pub fn free<'c, F>(&'c self, f: &'c mut F) -> bool where F: FnMut(TyVar<'a>) -> bool, 'a: 'c {
        match *self {
            Ty::Quant(ref a, t) => t.free(&mut |a_| {
                // Want TyVars that are free in t but aren't included in our quantifiers.
                if a.iter().any( |&a| a_ == a ) { return true }
                //println!("{:?} free in {:?}", a_, a);
                // Now we know that this is the case, so run the function.
                f(a_)
            })
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
                write!(f, "{:?}", union_find::find(*ty).ty.get())
            },
        }
    }
}

