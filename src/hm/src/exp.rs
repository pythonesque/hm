use self::Exp as E;
use util::symbol::{Symbol, Symbols};

use std::fmt;

pub type Var<'a> = Symbol<'a>;

pub enum Exp<'a> {
    Var(Var<'a>),
    Abs(Var<'a>, Box<Exp<'a>>),
    App(Box<Exp<'a>>, Box<Exp<'a>>),
    Let(Var<'a>, Box<Exp<'a>>, Box<Exp<'a>>),
}

impl<'a> fmt::Display for Exp<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            E::Var(ref x) => Symbols::new().fmt(f, x),
            E::Abs(ref x, ref e) => {
                try!(write!(f, "λ"));
                try!(Symbols::new().fmt(f, x));
                write!(f, ". {}", e)
            },
            E::App(ref e1, ref e2) => {
                write!(f, "{} {}", e1, e2)
            },
            E::Let(ref x, ref e1, ref e2) => {
                try!(write!(f, "let "));
                try!(Symbols::new().fmt(f, x));
                write!(f, " = {} in {}", e1, e2)
            },
        }
    }
}

pub mod parse {
    use self::ErrorKind as EK;
    use self::Tok as T;
    use super::Exp as E;
    use util::symbol::{Symbol, Symbols};

    use std::fmt;

    #[derive(Debug)]
    enum Tok<'a> {
        Ident(&'a str),
        Lambda,
        Let,
        In,
        EOF,
    }

    #[derive(Clone,Copy,Debug)]
    pub struct Error {
        pub pos: usize,
        pub kind: ErrorKind,
    }

    #[derive(Clone,Copy,Debug)]
    pub enum ErrorKind {
        Parse,
        Symbol,
    }

    pub type Res<T> = Result<T, Error>;

    impl fmt::Display for Error {
        fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
            write!(f, "Inference failure.")
        }
    }

    fn read_tok<'a>(ctx: Ctx<'a>) -> (Tok<'a>, Ctx<'a>) {
        let s = ctx.s.trim_left();
        let pos = s.len();
        let tok_len = s.chars().take_while( |&ch| !ch.is_whitespace() ).count();
        if tok_len == 0 { return (T::EOF, Ctx { s: s, pos: pos }) }
        (match &s[..tok_len] {
            "lambda" => T::Lambda,
            "let" => T::Let,
            "in" => T::In,
            i => T::Ident(i)
        }, Ctx { s: &s[tok_len..], pos: pos + tok_len })
    }

    #[derive(Clone,Copy)]
    struct Ctx<'a> {
        s: &'a str,
        pos: usize,
    }

    type PRes<'a> = Res<(E<'a>, Ctx<'a>)>;

    fn err<'a,T>(ctx: Ctx<'a>, kind: EK) -> Res<T> {
        Err(Error { pos: ctx.pos, kind: kind })
    }

    fn sym<'a>(ctx: Ctx<'a>, name: &'a str, symbols: &mut Symbols<'a>) -> Res<Symbol<'a>> {
        symbols.symbol(name).or_else( |_| err(ctx, EK::Symbol))
    }

    fn parse_sym<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> Res<(Symbol<'a>, Ctx<'a>)> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::Ident(i) => Ok((try!(sym(ctx, i, symbols)), rest)),
            _ => err(ctx, EK::Parse)
        }
    }

    fn parse_abs<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (x, rest) = try!(parse_sym(ctx, symbols));
        let (e, rest) = try!(parse_exp(rest, symbols));
        Ok((E::Abs(x, Box::new(e)), rest))
    }

    fn parse_let<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (x, rest) = try!(parse_sym(ctx, symbols));
        let (e1, rest) = try!(parse_exp(rest, symbols));
        let rest = match read_tok(rest) {
            (T::In, rest) => rest,
            _ => return err(rest, EK::Parse)
        };
        let (e2, rest) = try!(parse_exp(rest, symbols));
        Ok((E::Let(x, Box::new(e1), Box::new(e2)), rest))
    }

    fn parse_app<'a>(mut ctx: Ctx<'a>, symbols: &mut Symbols<'a>, mut e1: E<'a>) -> PRes<'a> {
        loop {
            let (tok, rest) = read_tok(ctx);
            let (e2, rest) = match tok {
                T::EOF | T::In => return Ok((e1, ctx)),
                T::Ident(i) => (E::Var(try!(sym(ctx, i, symbols))), rest),
                T::Lambda => try!(parse_abs(rest, symbols)),
                T::Let => try!(parse_let(rest, symbols)),
            };
            e1 = E::App(Box::new(e1), Box::new(e2));
            ctx = rest;
        }
    }

    fn parse_exp<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        let (exp, rest) = match tok {
            T::Ident(i) => (E::Var(try!(sym(ctx, i, symbols))), rest),
            T::Lambda => try!(parse_abs(rest, symbols)),
            T::Let => try!(parse_let(rest, symbols)),
            _ => return err(ctx, EK::Parse),
        };
        parse_app(rest, symbols, exp)
    }

    fn parse_prog<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        parse_exp(ctx, symbols)
            .and_then( |(exp,rest)| match read_tok(rest) {
                (T::EOF, rest) => Ok((exp, rest)),
                _ => err(rest, EK::Parse),
            } )
    }

    pub fn parse<'a>(s: &'a str, symbols: &mut Symbols<'a>) -> Res<E<'a>> {
        parse_prog(Ctx { s: s, pos: 0 }, symbols)
            .map( |(exp,_)| exp )
    }
}
