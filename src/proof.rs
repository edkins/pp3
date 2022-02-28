use crate::axioms;
use crate::formula::{FormulaBuilder, FormulaPackage, FreeVar};
use crate::globals::{self, Globals};
use crate::script::{Line, Script};

pub struct ProofContext {
    hypotheses: Vec<FormulaPackage>,
    theorems: Vec<FormulaPackage>,
    num_free_vars: u32,
}

#[derive(Debug)]
pub enum ProofError {
    CouldNotProve(String),
}

impl ProofContext {
    pub fn new(g: &Globals) -> Self {
        let hypotheses = vec![];
        let theorems = axioms::axioms(g);
        let num_free_vars = 0;
        for theorem in &theorems {
            if theorem.num_free_vars() > num_free_vars {
                panic!("Too many free vars in theorem");
            }
        }
        ProofContext {
            hypotheses,
            theorems,
            num_free_vars,
        }
    }

    pub fn print(&self, g: &Globals) {
        if self.num_free_vars > 0 || !self.hypotheses.is_empty() {
            for hypothesis in &self.hypotheses {
                println!("assume {}", hypothesis.formula().to_string(g));
            }
            println!("---------------------");
        }
        for theorem in &self.theorems {
            println!("conclude {}", theorem.formula().to_string(g));
        }
    }

    fn suppose(&self, _g: &Globals, hyp: &FormulaPackage) -> Self {
        if hyp.num_free_vars() > self.num_free_vars {
            panic!("Too many free vars in hypothesis");
        }
        let mut hypotheses = self.hypotheses.clone();
        hypotheses.push(hyp.clone());
        ProofContext {
            hypotheses,
            theorems: vec![hyp.clone()],
            num_free_vars: self.num_free_vars,
        }
    }

    fn introduce(&self, _g: &Globals, var: FreeVar) -> Self {
        if var.index() != self.num_free_vars {
            panic!("Introducing the wrong variable");
        }
        ProofContext {
            hypotheses: self.hypotheses.clone(),
            theorems: vec![],
            num_free_vars: self.num_free_vars + 1,
        }
    }

    fn conclusion(&self) -> &FormulaPackage {
        &self.theorems[self.theorems.len() - 1]
    }

    fn attempt_to_prove(&self, g: &Globals, f: &FormulaPackage) -> bool {
        false
    }

    pub fn process(&mut self, g: &mut Globals, script: &Script) -> Result<(), ProofError> {
        for line in script.lines() {
            match line {
                Line::Formula(f) => {
                    if f.num_free_vars() > self.num_free_vars {
                        panic!("Too many free vars in script formula");
                    }
                    if !self.attempt_to_prove(g, f) {
                        return Err(ProofError::CouldNotProve(f.formula().to_string(g)));
                    }
                    self.theorems.push(f.clone());
                }
                Line::Forall(x, bx) => {
                    let mut context = self.introduce(g, *x);
                    context.process(g, bx)?;
                    let mut fb = FormulaBuilder::default();
                    fb.quantify_free_var(g, context.conclusion().formula(), *x, false);
                    self.theorems.push(fb.finish(g, self.num_free_vars));
                }
                Line::Imp(hyp, bx) => {
                    let mut context = self.suppose(g, hyp);
                    context.process(g, bx)?;
                    let mut fb = FormulaBuilder::default();
                    fb.push_global(g, globals::IMP);
                    fb.push_formula(g, hyp.formula());
                    fb.push_formula(g, context.conclusion().formula());
                }
            }
        }
        Ok(())
    }
}
