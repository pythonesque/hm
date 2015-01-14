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
static _NO_CHECKED_ADD_NEEDED: bool = usize::BITS <= u8::MAX as usize;

/// Cannot implement Clone and retain correct semantics.
#[derive(Show)]
pub struct UnionFind<'a, T: ?Sized> where T: 'a {
    parent: Cell<Option<&'a T>>,
    rank: Cell<u8>
}

impl<'a, T> PartialEq for UnionFind<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }
}

pub trait UnionFindable<'a> {
    fn copy<F>(&'a self, init: F) -> Self where Self: Sized, F: FnOnce(UnionFind<'a, Self>) -> Self {
        let oroot = self.find();
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

    fn as_union_find<'b>(&'b self) -> &'b UnionFind<'a, Self>;

    fn on_union<'b>(&'b self, parent: &'a Self);

    fn find(&'a self) -> &'a Self {
        let x = self.as_union_find();
        match x.parent.get() {
            Some(p) => {
                let p = p.find();
                x.parent.set(Some(p));
                p
            },
            None => self
        }
    }

    fn union(&'a self, other: &'a Self) {
        let root = self.find();
        let oroot = other.find();
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

    /*/// Sometimes this can be used instead of Clone
    fn copy_union_find(&'a self) -> UnionFind<'a, Self> {
        let new = UnionFind {
            parent: Cell::new(Some(self.find())),
            rank: Cell::new(0),
        };
        new
    }*/
}

impl<'a,T> UnionFind<'a, T> where T: UnionFindable<'a> + 'a {
    pub fn new() -> Self {
        UnionFind {
            parent: Cell::new(None),
            rank: Cell::new(0)
        }
    }
}
