use crate::formula::FormulaPackage;
use crate::globals::Globals;
use crate::parse;

// Index of axioms
pub const add_0_r:usize = 0;
pub const add_succ_r:usize = 1;
pub const num_axioms:usize = 2;

pub fn axioms(g: &Globals) -> Vec<FormulaPackage> {
    let mut result = vec![FormulaPackage::dummy(0); num_axioms];
    result[add_0_r] = parse::parse_sentence(g, "forall x:nat (x + 0 = x)").unwrap();
    result[add_succ_r] = parse::parse_sentence(g, "forall x:nat (forall y:nat (x + (y + 1) = (x + y) + 1))").unwrap();
    result
}

#[cfg(test)]
mod test {
    use crate::axioms::*;

    #[test]
    fn axioms_parse_ok() {
        let g = Globals::default();
        axioms(&g);
    }
}
