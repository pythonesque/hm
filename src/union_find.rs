use std::cmp::{Ord, Ordering};
use std::cell::Cell;
use std::intrinsics;
use std::num::Int;
use std::uint;
use std::u8;

/// Max rank of a k-element Union-Find tree with path compression is lg(k).
///
/// [source](http://ocw.mit.edu/courses/electrical-engineering-and-computer-science/6-046j-design-and-analysis-of-algorithms-spring-2012/lecture-notes/MIT6_046JS12_lec16.pdf)
///
/// So if uint::BITS <= u8::MAX, we don't have to perform any checks at all for builtin integer
/// types to never overflow.  In theory we should constrain it so users can't specify their own
/// types though.
#[static_assert]
static NO_CHECKED_ADD_NEEDED: bool = uint::BITS <= u8::MAX as uint;

/// Cannot implemenet Clone and retain correct semantics.
pub struct UnionFind<'a, I=u32> where I: 'static, I: Copy {
    parent: Cell<Option<&'a UnionFind<'a,I>>>,
    rank: Cell<I>
}


impl<'a,I> UnionFind<'a, I> where I: Int + 'static {
    pub fn new() -> UnionFind<'a, I> {
        UnionFind {
            parent: Cell::new(None),
            rank: Cell::new(Int::zero())
        }
    }

    pub fn find(&'a self) -> &'a Self {
        match self.parent.get() {
            Some(p) => {
                let p = p.find();
                self.parent.set(Some(p));
                p
            },
            None => self
        }
    }

    /// Sometimes this can be used instead of Clone
    pub fn copy(&'a self) -> UnionFind<'a, I> {
        let new = UnionFind {
            parent: Cell::new(Some(self.find())),
            rank: Cell::new(Int::zero()),
        };
        new
    }

    pub fn union(&'a self, other: &'a Self) {
        let root = self.find();
        let oroot = other.find();
        if root as *const _ == oroot as *const _ { return }
        let rank = root.rank.get();
        match rank.cmp(&oroot.rank.get()) {
            Ordering::Less => root.parent.set(Some(oroot)),
            Ordering::Greater => oroot.parent.set(Some(root)),
            Ordering::Equal => {
                oroot.parent.set(Some(root));
                root.rank.set(rank + Int::one());
            }
        }
    }
}
