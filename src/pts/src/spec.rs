use exp::Const;

pub type Sort<'a> = Const<'a>;

pub type Axioms<'a> = Vec<(Const<'a>, Sort<'a>)>;

pub type Rules<'a> = Vec<(Sort<'a>, Sort<'a>, Sort<'a>)>;

pub struct Spec<'a> {
    axioms: Axioms<'a>,
    rules: Rules<'a>
}
