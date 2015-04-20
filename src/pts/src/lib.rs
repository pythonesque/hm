#![feature(box_patterns)]
#![cfg_attr(test, feature(test))]

extern crate util;

pub use exp::parse::parse;

pub mod exp;
pub mod spec;

#[cfg(test)]
mod tests {
    extern crate test;

    use super::{parse};

    fn bench<'a,B,F>(mut b: B, closure: F)
        where F: Fn(),
              B: FnMut(&mut FnMut())
    {
        b( &mut || {
            closure();
        });
    }

    static TRIVIAL: &'static str = r"n";

    static BINARY_PRODUCTS: &'static str = r"
pi () lambda r 0 . r .
pi prod lambda e1 1 . lambda e2 2 .
    lambda x 3 . x e1 e2 .
pi left lambda e 4 .
    e lambda x 5 . lambda y 6 . x .
pi right lambda e 5 .
    e lambda x 6 . lambda y 7 . y .

pi p prod n false .
right p
";

    static BINARY_SUMS: &'static str = r"
pi void r .
pi abort lambda e 0 . e .
pi Left lambda e 1 .
    lambda x 2 . lambda y 3 . x e .
pi Right lambda e 4 .
    lambda x 5 . lambda y 6 . y e .
pi case lambda e 7 . lambda l 8 . lambda r 9 .
    e l r .

pi f lambda f 10 .
    pi s Right true .
    pi t Left n .
    pi _ f s .
    pi _ f t .
    pi l lambda x1 11 . false .
    pi r lambda x2 12 . x2 .
    case s l r
. f lambda x 13 . lambda y 14 . y
";

    static OCCURS_CHECK: &'static str = r"
pi foo lambda x 0 . x x .
foo
";

    #[test]
    fn it_works() {

        let exp1 = parse("pi id lambda x 0 . x . id n").unwrap();
        let exp2 = parse("
pi bar lambda x 0 .
    pi foo lambda y 1 . x
    . foo
. bar").unwrap();
        let exp3 = parse(BINARY_PRODUCTS).unwrap();
        let exp4 = parse(BINARY_SUMS).unwrap();
        let exp5 = parse(OCCURS_CHECK).unwrap();
        bench(|t| t(), move || {
            println!("{}", exp1);
            println!("{}", exp2);
            println!("{}", exp3);
            println!("{}", exp4);
            println!("{}", exp5);
        });
    }

    #[bench]
    fn bench_trivial_hm(b: &mut test::Bencher) {
        let _exp = parse(TRIVIAL).unwrap();
        bench(|t| b.iter(|| t()), move || {
        });
    }

    #[bench]
    fn bench_binary_products_hm(b: &mut test::Bencher) {
        let _exp = parse(BINARY_PRODUCTS).unwrap();
        bench(|t| b.iter(|| t()), move || {
        });
    }

    #[bench]
    fn bench_binary_sums_hm(b: &mut test::Bencher) {
        let _exp = parse(BINARY_SUMS).unwrap();
        bench(|t| b.iter(|| t()), move || {
        });
    }
}
