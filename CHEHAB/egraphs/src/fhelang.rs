use egg::*;
use std::fmt;

define_language! {
    pub enum FheLang {
        Constant(i32),
        "+" = Add([Id; 2]),
        "*" = Mul([Id; 2]),
        "-" = Minus([Id; 2]),
        "<<" = Rot([Id; 2]),
        "SumVec" = SumVec([Id; 2]),
        "-" = Neg([Id; 1]),
        "square" = Square([Id; 1]),
         "%" = Mod([Id; 2]),
        Symbol(egg::Symbol),

    }
}
impl fmt::Display for FheLang {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FheLang::Constant(val) => write!(f, "{}", val),
            FheLang::Add(ids) => write!(f, "+"),
            FheLang::Mul(ids) => write!(f, "*"),
            FheLang::Minus(ids) => write!(f, "-"),
            FheLang::Rot(ids) => write!(f, "<<"),
            FheLang::SumVec(ids) => write!(f, "SumVec"),
            FheLang::Neg(ids) => write!(f, "-"),
            FheLang::Square(ids) => write!(f, "square"),
            FheLang::Mod(ids) => write!(f, "%"),
            FheLang::Symbol(sym) => write!(f, "{}", sym),  
        }
    }
}
#[derive(Default, Clone)]
pub struct ConstantFold;

pub type Egraph = egg::EGraph<FheLang, ConstantFold>;

impl Analysis<FheLang> for ConstantFold {
    type Data = Option<i32>;
    fn make(egraph: &Egraph, enode: &FheLang) -> Self::Data {
        let x = |i: &Id| egraph[*i].data.as_ref();
        Some(match enode {
            FheLang::Constant(c) => *c,
            FheLang::Add([a, b]) => x(a)? + x(b)?,
            FheLang::Minus([a, b]) => x(a)? - x(b)?,
            FheLang::Mul([a, b]) => x(a)? * x(b)?,
            FheLang::Mod([a, b]) => x(a)? % x(b)?,
            FheLang::Neg([a]) => -*x(a)?,
            FheLang::SumVec([a, _b]) => *x(a)?,
            FheLang::Rot([a, _b]) => *x(a)?,
            _ => return None,
        })
    }

    fn merge(& self, to: &mut Self::Data, from: Self::Data) -> bool {
        match (to.as_mut(), &from) {
            (None, Some(_)) => true,
            (_, _) => false,/*Match the rest of combinations */
        }
    }
    
    fn modify(egraph: &mut Egraph, id: Id) {
        let class = &mut egraph[id];
        if let Some(c) = class.data.clone() {
            let added = egraph.add(FheLang::Constant(c.clone()));
            let (id, _did_something) = egraph.union(id, added);
            // to not prune, comment this out
            egraph[id].nodes.retain(|n| n.is_leaf());

            assert!(
                !egraph[id].nodes.is_empty(),
                "empty eclass! {:#?}",
                egraph[id]
            );
            #[cfg(debug_assertions)]
            egraph[id].assert_unique_leaves();
        }
    }
}
