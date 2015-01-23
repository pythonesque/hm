use rustc::util::nodemap::FnvHashMap;
use std::collections::hash_map::{self, Entry, HashMap};
use std::fmt::{self, String};
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
    pub fn name(&self, symbol: &Symbol<'a>) -> Option<&'a str> {
        symbol.0
    }

    pub fn fmt(&self, f: &mut fmt::Formatter, symbol: &Symbol<'a>) -> fmt::Result {
        match *symbol {
            Symbol(Some(name),_) => name.fmt(f),
            Symbol(_,i) => i.fmt(f),
        }
    }

    pub fn symbol(&mut self, name: &'a str) -> Result<Symbol<'a>, ()> {
        let Symbols {ref mut symbols, ref mut next_sym } = *self;
        Ok(match symbols.entry(name) {
            Entry::Occupied(o) => Symbol(Some(name), *o.get()),
            Entry::Vacant(v) => Symbol(Some(name), *v.insert(try!(get_next_sym(next_sym)))),
        })
    }

    /// Taking self is future proofing (if we need to shrink variable sizes).
    pub fn empty<'b, 'c, T>(&'b self) -> Table<'c, T> {
        Table {
            table: FnvHashMap::new(),
        }
    }
}

#[derive(Clone)]
pub struct Table<'a, T> {
    table: FnvHashMap<S, T>,
}

pub struct Values<'a, T>(hash_map::Values<'a, S, T>) where T: 'a;

impl<'a, T> Iterator for Values<'a, T> where T: 'a {
    type Item = &'a T;

    fn next(&mut self) -> Option<&'a T> {
        self.0.next()
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.0.size_hint()
    }
}

impl<'a, T> Table<'a, T> {
    pub fn enter<'b>(&mut self, k: &'b Symbol<'a>, v: T) -> Option<T> {
        self.table.insert(k.1, v)
    }

    pub fn delete(&mut self, k: &Symbol<'a>) -> Option<T> {
        self.table.remove(&k.1)
    }

    pub fn look<'b,'c>(&'b self, k: &'c Symbol<'a>) -> Option<&'b T> {
        self.table.get(&k.1)
    }

    pub fn values<'b>(&'b self) -> Values<'b,T> {
        Values(self.table.values())
    }

    pub fn fmt(&self, f: &mut fmt::Formatter, symbols: &Symbols<'a>) -> fmt::Result
        where T: fmt::String
    {
        try!(write!(f, "{{"));
        let mut iter = self.table.iter();
        if let Some((i,v)) = iter.next() {
            let reverse_map = symbols.symbols.iter()
                                             .map( |(&i, &name)| (name, i) )
                                             .collect::<HashMap<_,_>>();
            let name = |&: i| Symbol(reverse_map.get(i).map( |&name| name ), *i);
            try!(symbols.fmt(f, &name(i)));
            try!(write!(f, ": {}", v));
            for (i, v) in iter {
                try!(write!(f, ", "));
                try!(symbols.fmt(f, &name(i)));
                try!(write!(f, ": {}", v));
            }
        }
        write!(f, "}}")
    }
}
