use crate::formula::FormulaPackage;
use crate::globals::Globals;
use crate::parse;

// Index of axioms
pub const ADD_0_R: usize = 0;
pub const ADD_SUCC_R: usize = 1;
pub const NUM_AXIOMS: usize = 2;

pub fn axioms(g: &Globals) -> Vec<FormulaPackage> {
    let mut result = vec![FormulaPackage::dummy(0); NUM_AXIOMS];
    result[ADD_0_R] = parse::parse_sentence(g, "forall x:nat (x + 0 = x)").unwrap();
    result[ADD_SUCC_R] =
        parse::parse_sentence(g, "forall x:nat (forall y:nat (x + (y + 1) = (x + y) + 1))")
            .unwrap();
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
