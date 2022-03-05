use crate::formula::{Formula, FormulaBuilder, FormulaPackage, FormulaReader, FreeVar, Outermost};
use crate::globals::Globals;
use crate::proof::ProofContext;
use crate::script::{Line, Script};

#[derive(Debug)]
pub enum ProofError {}

pub struct TacticContext {
    pc: ProofContext,
    extra: Vec<Extra>,
}

enum Extra {
    Layers(Vec<FormulaPackage>),
    Ignore,
}

struct AugmentedFormula<'a> {
    formula: Formula<'a>,
    extra: &'a Extra,
}

fn gen_extra(g: &Globals, f: Formula<'_>, num_free_vars: u32) -> Vec<FormulaPackage> {
    let mut result = vec![];
    match f.outermost() {
        Outermost::Forall => {
            let mut fb = FormulaBuilder::default();
            let var = FreeVar::new(num_free_vars);
            fb.subst_quantified_var_with_free_var(g, f, var, false);
            result.push(fb.finish(g, num_free_vars + 1));
            let f2 = result[result.len() - 1].formula();
            let rest = gen_extra(g, f2, num_free_vars + 1);
            result.extend(rest);
        }
        Outermost::Imp => {
            let mut reader = FormulaReader::new(f);
            reader.expect_imp(g).unwrap();
            let _ = reader.read_formula(g);
            let f2 = reader.read_formula(g);
            reader.end();
            let rest = gen_extra(g, f2, num_free_vars);
            result.extend(rest);
        }
        Outermost::Other => {}
    }
    result
}

impl TacticContext {
    pub fn new(g: &Globals, pc: ProofContext) -> Self {
        let mut result = TacticContext { pc, extra: vec![] };
        for i in 0..result.pc.num_formulas() {
            let extra = result.gen_extra(g, result.pc.formula(i));
            result.extra.push(extra);
        }
        result
    }

    fn get_augmented_formula(&self, i: usize) -> AugmentedFormula<'_> {
        AugmentedFormula {
            formula: self.pc.formula(i),
            extra: &self.extra[i],
        }
    }

    fn gen_extra(&self, g: &Globals, f: Formula<'_>) -> Extra {
        let layers = gen_extra(g, f, self.pc.num_free_vars());
        Extra::Layers(layers)
    }

    /*
    fn attempt_to_prove_immediately(&self, g: &Globals, f: &FormulaPackage) -> bool {
        for theorem in &self.theorems {
            if let Some(deps) = theorem.proof_dependencies(g, f) {
                if deps.is_empty() {
                    return true;
                }
            }
        }
        false
    }

    fn attempt_to_prove(&self, g: &Globals, f: &FormulaPackage) -> bool {
        for theorem in &self.theorems {
            if let Some(deps) = &theorem.proof_dependencies(g, f) {
                let mut proved = true;
                for dep in deps {
                    if !self.attempt_to_prove_immediately(g, dep) {
                        proved = false;
                        break;
                    }
                }
                if proved {
                    return true;
                }
            }
        }
        false
    }
    */

    pub fn process(&mut self, g: &mut Globals, script: &Script) -> Result<(), ProofError> {
        for line in script.lines() {
            match line {
                Line::Formula(f) => {
                    if f.num_free_vars() > self.pc.num_free_vars() {
                        panic!("Too many free vars in script formula");
                    }
                    /*if !self.attempt_to_prove(g, f) {
                        return Err(ProofError::CouldNotProve(f.formula().to_string(g)));
                    }
                    self.theorems.push(f.clone());*/
                }
                Line::Forall(x, bx) => {
                    self.pc.begin_forall_box(g, *x);
                    let result = self.process(g, bx);
                    self.pc.end_forall_box(g);
                    result?;
                }
                Line::Imp(hyp, bx) => {
                    self.pc.begin_imp_box(g, hyp);
                    let result = self.process(g, bx);
                    self.pc.end_imp_box(g);
                    result?;
                }
            }
        }
        Ok(())
    }
}
