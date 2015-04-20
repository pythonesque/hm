use exp::Const;

pub type Sort = Const;

pub type Axioms = Vec<(Const, Sort)>;

// Only dealing with functional PTSes for the time being.
pub type Rules = Vec<(Sort, Sort)>;

pub struct Spec {
    axioms: Axioms,
    rules: Rules,
}
