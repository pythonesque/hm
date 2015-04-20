use self::Exp as E;

use std::fmt;

pub type Var = u32; // De Bruijn index

pub type Const = u32;

pub enum Exp {
    Var(Var),
    Const(Const),
    Abs(Box<(Exp, Exp)>),
    App(Box<(Exp, Exp)>),
    Prod(Box<(Exp, Exp)>),
}

impl<'a> fmt::Display for Exp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match *self {
            E::Var(ref x) => x.fmt(f),
            E::Const(ref x) => write!(f, "S{}", x),
            E::Abs(box (ref e1, ref e2)) => {
                write!(f, "λ({}). {}", e1, e2)
            },
            E::App(box (ref e1, ref e2)) => {
                write!(f, "{} {}", e1, e2)
            },
            E::Prod(box (ref e1, ref e2)) => {
                write!(f, "Π({}). {}", e1, e2)
            },
        }
    }
}

pub mod parse {
    use self::ErrorKind as EK;
    use self::Tok as T;
    use super::{Const, Var};
    use super::Exp as E;

    use std::collections::VecDeque;
    use std::fmt;

    #[derive(Debug)]
    enum Tok<'a> {
        Ident(&'a str),
        Nat(&'a str),
        Lambda,
        Pi,
        Dot,
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
        NatOverflow,
        DeBruijnOverflow
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

        let tok_len = s.chars().take_while( |&ch| ch.is_digit(10) ).count();
        if tok_len != 0 {
            return (T::Nat(&s[..tok_len]), Ctx { s: &s[tok_len..], pos: pos + tok_len });
        }

        let tok_len =
            if s.chars().next().map_or(false, |ch| ch == '.') { 1 }
            else { s.chars().take_while( |&ch| !ch.is_whitespace() && ch != '.' ).count() };
        if tok_len == 0 { return (T::EOF, Ctx { s: s, pos: pos }) }
        (match &s[..tok_len] {
            "lambda" => T::Lambda,
            "pi" => T::Pi,
            "." => T::Dot,
            i => T::Ident(i)
        }, Ctx { s: &s[tok_len..], pos: pos + tok_len })
    }

    #[derive(Clone,Copy)]
    struct Ctx<'a> {
        s: &'a str,
        pos: usize,
    }

    struct Env<'a> {
        vars: VecDeque<&'a str>, // Rightmost in vector = innermost bound variable
    }

    type PRes<'a> = Res<(E, Ctx<'a>)>;

    fn err<'a,T>(ctx: Ctx<'a>, kind: EK) -> Res<T> {
        Err(Error { pos: ctx.pos, kind: kind })
    }

    fn parse_sym<'a>(ctx: Ctx<'a>) -> Res<(&'a str, Ctx<'a>)> {
        let (tok, rest) = read_tok(ctx);
        match tok {
            T::Ident(i) => Ok((i, rest)),
            _ => err(ctx, EK::Parse)
        }
    }

    fn parse_var<'a>(ctx: Ctx<'a>, tok: &'a str, env: &mut Env<'a>) -> Res<Var> {
        match env.vars.iter().rev().position( |&v| v == tok) {
            Some(idx) => Ok(idx as Var),
            None => {
                let idx = env.vars.len() as Var;
                match idx.checked_add(1) {
                    Some(_) => {
                        // Total number free <= total length, so safe to add a free var
                        // (Might be able to squeeze in one more, but is it really worth it?)
                        env.vars.push_front(tok);
                        Ok(idx)
                    },
                    None => err(ctx, EK::DeBruijnOverflow)
                }
            }
        }
    }

    fn parse_const<'a>(ctx: Ctx<'a>, tok: &'a str) -> Res<Const> {
        match tok.parse() {
            Ok(n) => Ok(n),
            Err(_) => err(ctx, EK::NatOverflow)
        }
    }

    fn bind_var<'a>(ctx: Ctx<'a>, tok: &'a str, env: &mut Env<'a>) -> Res<()> {
        match (env.vars.len() as Var).checked_add(1) {
            Some(_) => {
                // Safe to add another variable
                env.vars.push_back(tok);
                Ok(())
            },
            None => err(ctx, EK::DeBruijnOverflow)
        }
    }

    fn parse_abs<'a>(ctx: Ctx<'a>, env: &mut Env<'a>) -> PRes<'a> {
        let (x, rest) = try!(parse_sym(ctx));
        let (e1, rest) = try!(parse_exp(rest, env));
        let rest = match read_tok(rest) {
            (T::Dot, rest) => rest,
            _ => return err(rest, EK::Parse)
        };
        try!(bind_var(ctx, x, env));
        let (e2, rest) = try!(parse_exp(rest, env));
        env.vars.pop_back();
        Ok((E::Abs(Box::new((e1, e2))), rest))
    }

    fn parse_prod<'a>(ctx: Ctx<'a>, env: &mut Env<'a>) -> PRes<'a> {
        let (x, rest) = try!(parse_sym(ctx));
        let (e1, rest) = try!(parse_exp(rest, env));
        let rest = match read_tok(rest) {
            (T::Dot, rest) => rest,
            _ => return err(rest, EK::Parse)
        };
        try!(bind_var(ctx, x, env));
        let (e2, rest) = try!(parse_exp(rest, env));
        env.vars.pop_back();
        Ok((E::Prod(Box::new((e1, e2))), rest))
    }

    fn parse_app<'a>(mut ctx: Ctx<'a>, env: &mut Env<'a>, mut e1: E) -> PRes<'a> {
        loop {
            let (tok, rest) = read_tok(ctx);
            let (e2, rest) = match tok {
                T::EOF | T::Dot => return Ok((e1, ctx)),
                T::Ident(i) => (E::Var(try!(parse_var(ctx, i, env))), rest),
                T::Nat(i) => (E::Const(try!(parse_const(ctx, i))), rest),
                T::Lambda => try!(parse_abs(rest, env)),
                T::Pi => try!(parse_prod(rest, env)),
            };
            e1 = E::App(Box::new((e1, e2)));
            ctx = rest;
        }
    }

    fn parse_exp<'a>(ctx: Ctx<'a>, env: &mut Env<'a>) -> PRes<'a> {
        let (tok, rest) = read_tok(ctx);
        let (exp, rest) = match tok {
            T::Ident(i) => (E::Var(try!(parse_var(ctx, i, env))), rest),
            T::Nat(i) => (E::Const(try!(parse_const(ctx, i))), rest),
            T::Lambda => try!(parse_abs(rest, env)),
            T::Pi => try!(parse_prod(rest, env)),
            _ => return err(ctx, EK::Parse),
        };
        parse_app(rest, env, exp)
    }

    fn parse_prog<'a>(ctx: Ctx<'a>, env: &mut Env<'a>) -> PRes<'a> {
        parse_exp(ctx, env)
            .and_then( |(exp,rest)| match read_tok(rest) {
                (T::EOF, rest) => Ok((exp, rest)),
                _ => err(rest, EK::Parse),
            } )
    }

    pub fn parse<'a>(s: &'a str) -> Res<E> {
        parse_prog(Ctx { s: s, pos: 0 }, &mut Env { vars: VecDeque::new() })
            .map( |(exp,_)| exp )
    }
}
