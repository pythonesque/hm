use std::cmp::{Ord, Ordering};
use std::cell::Cell;
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
static _NO_CHECKED_ADD_NEEDED: bool = uint::BITS <= u8::MAX as uint;

/// Cannot implemenet Clone and retain correct semantics.
#[derive(Show)]
pub struct UnionFind<'a> {
    parent: Cell<Option<&'a UnionFind<'a>>>,
    rank: Cell<u8>
}

impl<'a> PartialEq for UnionFind<'a> {
    fn eq(&self, other: &Self) -> bool {
        self as *const _ == other as *const _
    }
}

impl<'a> UnionFind<'a> {
    pub fn new() -> UnionFind<'a> {
        UnionFind {
            parent: Cell::new(None),
            rank: Cell::new(0)
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
    pub fn copy(&'a self) -> UnionFind<'a> {
        let new = UnionFind {
            parent: Cell::new(Some(self.find())),
            rank: Cell::new(0),
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
                root.rank.set(rank + 1);
            }
        }
    }
}
