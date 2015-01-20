use self::Exp as E;
use symbol::{Symbol, Symbols};

use std::fmt;

pub type Var<'a> = Symbol<'a>;

pub enum Exp<'a> {
    Var(Var<'a>),
    Abs(Var<'a>, Box<Exp<'a>>),
    App(Box<Exp<'a>>, Box<Exp<'a>>),
    Let(Var<'a>, Box<Exp<'a>>, Box<Exp<'a>>),
}

impl<'a> fmt::String for Exp<'a> {
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
    use symbol::{Symbol, Symbols};

    #[derive(Show)]
    enum Tok<'a> {
        Ident(&'a str),
        Lambda,
        Let,
        In,
        EOF,
    }

    #[derive(Copy,Show)]
    pub struct Error {
        pub pos: usize,
        pub kind: ErrorKind,
    }

    #[derive(Copy,Show)]
    pub enum ErrorKind {
        Parse,
        Symbol,
    }

    pub type Res<T> = Result<T, Error>;

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

    #[derive(Copy)]
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

    fn parse_abs<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::Ident(i) => {
                let x = try!(sym(ctx, i, symbols));
                let (e, rest) = try!(parse_exp(rest, symbols));
                Ok((E::Abs(x, Box::new(e)), rest))
            },
            _ => err(ctx, EK::Parse)
        }
    }

    fn parse_in<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>, x: Symbol<'a>, e1: E<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::In => {
                let (e2, rest) = try!(parse_exp(rest, symbols));
                Ok((E::Let(x, Box::new(e1), Box::new(e2)), rest))
            },
            _ => err(ctx, EK::Parse)
        }
    }

    fn parse_let<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::Ident(i) => {
                let x = try!(sym(ctx, i, symbols));
                let (e1, rest) = try!(parse_exp(rest, symbols));
                parse_in(rest, symbols, x, e1)
            },
            _ => err(ctx, EK::Parse)
        }
    }

    fn parse_app<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>, e1: E<'a>) -> PRes<'a> {
        let (tok, _) = read_tok(ctx);
        match tok {
            T::EOF | T::In => Ok((e1, ctx)),
            _ => {
                let (e2, rest) = try!(parse_exp(ctx, symbols));
                Ok((E::App(Box::new(e1), Box::new(e2)), rest))
            },
        }
    }

    fn parse_exp<'a>(ctx: Ctx<'a>, symbols: &mut Symbols<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::Ident(i) => {
                let e1 = E::Var(try!(sym(ctx, i, symbols)));
                parse_app(rest, symbols, e1)
            },
            T::Lambda => parse_abs(rest, symbols),
            T::Let => parse_let(rest, symbols),
            _ => err(ctx, EK::Parse),
        }
    }

    pub fn parse<'a>(s: &'a str, symbols: &mut Symbols<'a>) -> Res<E<'a>> {
        parse_exp(Ctx { s: s, pos: 0 }, symbols).map( |(exp,_)| exp )
    }
}
