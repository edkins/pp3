use crate::globals::Globals;
use crate::proof::{ProofContext, ProofError};
use crate::script::{Line,Script};

impl ProofContext {
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
                    if f.num_free_vars() > self.num_free_vars() {
                        panic!("Too many free vars in script formula");
                    }
                    /*if !self.attempt_to_prove(g, f) {
                        return Err(ProofError::CouldNotProve(f.formula().to_string(g)));
                    }
                    self.theorems.push(f.clone());*/
                }
                Line::Forall(x, bx) => {
                    self.begin_forall_box(g, *x);
                    let result = self.process(g, bx);
                    self.end_forall_box(g);
                    result?;
                }
                Line::Imp(hyp, bx) => {
                    self.begin_imp_box(g, hyp);
                    let result = self.process(g, bx);
                    self.end_imp_box(g);
                    result?;
                }
            }
        }
        Ok(())
    }
}
