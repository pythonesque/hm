use std::collections::hash_map::{HashMap, Entry};
use std::fmt::{self, Show};
use std::num::Int;

type S = u32;

#[derive(Copy,Clone,Eq,Hash,Show,PartialEq)]
pub struct Symbol<'a>(Option<&'a str>, S);

pub struct Symbols<'a> {
    next_sym: S,
    symbols: HashMap<&'a str, S>,
}

fn get_next_sym(next_sym: &mut S) -> Result<S,()> {
    let i = *next_sym;
    *next_sym = match i.checked_add(Int::one()) {
        Some(i) => i,
        None => return Err(())
    };
    Ok(i)
}

impl<'a> Symbols<'a> {
    pub fn new() -> Symbols<'a> {
        Symbols {
            next_sym: 0,
            symbols: HashMap::new(),
        }
    }

    pub fn fresh(&mut self) -> Result<Symbol<'a>, ()> {
        Ok(Symbol(None, try!(get_next_sym(&mut self.next_sym))))
    }

    /// Taking self is future proofing (if we need to shrink variable sizes).
    pub fn name<'b,'c>(&'b self, symbol: &'c Symbol<'c>) -> Option<&'c str> {
        symbol.0
    }

    pub fn fmt<'b,'c>(&'b self, f: &mut fmt::Formatter, symbol: &'c Symbol<'c>) -> fmt::Result {
        match *symbol {
            Symbol(Some(name),_) => name.fmt(f),
            Symbol(_,i) => i.fmt(f),
        }
    }

    pub fn symbol(&mut self, name: &'a str) -> Result<Symbol<'a>, ()> {
        let Symbols {ref mut symbols, ref mut next_sym } = *self;
        Ok(match symbols.entry(&name) {
            Entry::Occupied(o) => Symbol(Some(name), *o.get()),
            Entry::Vacant(v) => Symbol(Some(name), *v.insert(try!(get_next_sym(next_sym)))),
        })
    }

    /// Taking self is future proofing (if we need to shrink variable sizes).
    pub fn empty<'b, 'c, T>(&'b self) -> Table<'c, T> {
        Table {
            table: HashMap::new(),
        }
    }
}

#[derive(Clone,Show)]
pub struct Table<'a, T> {
    table: HashMap<S, T>,
}

impl<'a, T> Table<'a, T> {
    pub fn enter(&mut self, k: &Symbol, v: T) -> Option<T> {
        self.table.insert(k.1, v)
    }

    pub fn look<'b,'c>(&'b self, k: &'c Symbol<'a>) -> Option<&'b T> {
        self.table.get(&k.1)
    }
}
