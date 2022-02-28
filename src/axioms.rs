use crate::formula::FormulaPackage;
use crate::globals::Globals;
use crate::parse;

pub fn axioms(g: &Globals) -> Vec<FormulaPackage> {
    vec![
        parse::parse_sentence(g, "forall x:nat (x + 0 = x)").unwrap(),
        parse::parse_sentence(g, "forall x:nat (forall y:nat (x + (y + 1) = (x + y) + 1))")
            .unwrap(),
    ]
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
