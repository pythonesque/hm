use std::cmp::{Ord, Ordering};
use std::cell::Cell;
use std::usize;
use std::u8;

/// Max rank of a k-element Union-Find tree with path compression is lg(k).
///
/// [source](http://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-046j-design-and-analysis-of-algorithms-spring-2012/lecture-notes/MIT6_046JS12_lec16.pdf)
///
/// So if uint::BITS <= u8::MAX, we don't have to perform any checks at all for builtin integer
/// types to never overflow.  In theory we should constrain it so users can't specify their own
/// types though.
#[static_assert]
static _NO_CHECKED_ADD_NEEDED: bool = usize::BITS <= u8::MAX as u32;

// Cannot implement Clone and retain correct semantics.
#[derive(Debug)]
pub struct UnionFind<'a, T: ?Sized> where T: 'a {
    parent: Cell<Option<&'a T>>,
    rank: Cell<u8>
}

fn find_inner<'a, T: ?Sized>(uf: &'a T) -> &T where T: UnionFindable<'a> + 'a {
    let x = uf.as_union_find();
    match x.parent.get() {
        Some(p) => {
            let p = find(p);
            x.parent.set(Some(p));
            p
        },
        None => uf
    }
}

pub fn copy<'a, T: ?Sized, F>(uf: &'a T, init: F) -> T
    where T: UnionFindable<'a> + Sized + 'a,
          F: FnOnce(UnionFind<'a, T>) -> T,
{
    let oroot = find(uf);
    let yroot = oroot.as_union_find();
    // We know we are rank 0, so we can always point to the parent.
    if yroot.rank.get() == 0 { yroot.rank.set(1) }
    let root = init(UnionFind {
        parent: Cell::new(Some(oroot)),
        rank: Cell::new(0)
    });
    root.on_union(oroot);
    root
}

#[inline(always)]
pub fn find<'a, T: ?Sized>(uf: &'a T) -> &T where T: UnionFindable<'a> + 'a {
    let x = uf.as_union_find();
    match x.parent.get() {
        Some(p) => {
            let p = find_inner(p);
            x.parent.set(Some(p));
            p
        },
        None => uf
    }
}

#[inline]
pub fn find_immutable<'a, 'c, T: ?Sized>(uf: &'c T) -> &'c T
    where T: UnionFindable<'a> + 'a,
          'a: 'c,
{
    let x = uf.as_union_find();
    match x.parent.get() {
        Some(ref p) => find_immutable(*p),
        None => uf
    }
}

#[inline(always)]
pub fn union<'a, T: ?Sized>(uf: &'a T, other: &'a T) where T: UnionFindable<'a> + 'a {
        let root = find(uf);
        let oroot = find(other);
        let xroot = root.as_union_find();
        let yroot = oroot.as_union_find();
        if xroot as *const _ == yroot as *const _ { return }
        let rank = xroot.rank.get();
        match rank.cmp(&yroot.rank.get()) {
            Ordering::Less => {
                xroot.parent.set(Some(oroot));
                // We call on_union after setting the parent in case the implementor could somehow
                // mess up the algorithmic bounds by running before it was done.
                root.on_union(oroot);
            },
            Ordering::Greater => {
                yroot.parent.set(Some(root));
                oroot.on_union(root);
            },
            Ordering::Equal => {
                xroot.parent.set(Some(oroot));
                yroot.rank.set(rank + 1);
                root.on_union(oroot);
            }
        }
    }

pub trait UnionFindable<'a>: 'a {
    fn as_union_find<'b>(&'b self) -> &'b UnionFind<'a, Self>;

    fn on_union<'b>(&'b self, parent: &'a Self);

}

impl<'a,T> UnionFind<'a, T> where T: UnionFindable<'a> + 'a {
    pub fn new() -> Self {
        UnionFind {
            parent: Cell::new(None),
            rank: Cell::new(0)
        }
    }
}
