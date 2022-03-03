use crate::axioms;
use crate::formula::{FormulaBuilder, FormulaPackage, FreeVar};
use crate::globals::{self, Globals};
use crate::script::{Line, Script};

pub struct ProofContext {
    boxes: Vec<ProofBox>,
    facts: Vec<Fact>,
    num_free_vars: u32,
}

pub enum ProofBox {
    Forall(FreeVar),
    Imp(FormulaPackage),
}

pub struct Fact {
    num_boxes: usize,
    fact: FormulaPackage,
}

#[derive(Debug)]
pub enum ProofError {
    CouldNotProve(String),
}

impl ProofContext {
    pub fn new(g: &Globals) -> Self {
        let facts = axioms::axioms(g).into_iter().map(|fact| {
            if fact.num_free_vars() > 0 {
                panic!("Not expecting free vars in axiom");
            }
            Fact{num_boxes:0, fact}
        }).collect();
        ProofContext {
            boxes: vec![],
            facts,
            num_free_vars: 0,
        }
    }

    pub fn print(&self, g: &Globals) {
        let mut num_boxes_printed = 0;
        println!("<<<<");
        for fact in &self.facts {
            while num_boxes_printed < fact.num_boxes {
                match &self.boxes[num_boxes_printed] {
                    ProofBox::Forall(x) => println!("forall {x}"),
                    ProofBox::Imp(h) => println!("assume {}", h.formula().to_string(g)),
                }
                num_boxes_printed += 1;
            }
            println!("   {}", fact.fact.formula().to_string(g));
        }
        println!(">>>>");
    }

    pub fn num_free_vars(&self) -> u32 {
        self.num_free_vars
    }

    pub fn begin_imp_box(&mut self, _g: &Globals, hyp: &FormulaPackage) {
        if hyp.num_free_vars() > self.num_free_vars {
            panic!("Too many free vars in hypothesis");
        }
        self.boxes.push(ProofBox::Imp(hyp.clone()));
        self.facts.push(Fact{num_boxes: self.boxes.len(), fact: hyp.clone()});
    }

    pub fn begin_forall_box(&mut self, _g: &Globals, var: FreeVar) {
        if var.index() != self.num_free_vars {
            panic!("Introducing the wrong variable");
        }
        self.num_free_vars += 1;
        self.boxes.push(ProofBox::Forall(var));
    }

    pub fn end_imp_box(&mut self, g: &Globals) {
        if let Some(ProofBox::Imp(h)) = self.boxes.pop() {
            if let Some(conclusion) = self.facts.pop() {
                if conclusion.num_boxes <= self.boxes.len() {
                    panic!("imp box is empty");
                }
                loop {
                    if let Some(f) = self.facts.pop() {
                        if f.num_boxes <= self.boxes.len() {
                            self.facts.push(f);  // oops didn't mean to remove that one, put it back
                            break;
                        }
                    } else {
                        break;
                    }
                }
                let mut fb = FormulaBuilder::default();
                fb.push_global(g, globals::IMP);
                fb.push_formula(g, h.formula());
                fb.push_formula(g, conclusion.fact.formula());
                let fact = fb.finish(g, self.num_free_vars);
                self.facts.push(Fact{num_boxes:self.boxes.len(), fact});
            } else {
                panic!("imp box is empty");
            }
        } else {
            panic!("Not in an imp box");
        }
    }

    pub fn end_forall_box(&mut self, g: &Globals) {
        if let Some(ProofBox::Forall(x)) = self.boxes.pop() {
            if let Some(conclusion) = self.facts.pop() {
                if conclusion.num_boxes <= self.boxes.len() {
                    panic!("forall box is empty");
                }
                loop {
                    if let Some(f) = self.facts.pop() {
                        if f.num_boxes <= self.boxes.len() {
                            self.facts.push(f);  // oops didn't mean to remove that one, put it back
                            break;
                        }
                    } else {
                        break;
                    }
                }
                self.num_free_vars -= 1;
                let mut fb = FormulaBuilder::default();
                fb.quantify_free_var(g, conclusion.fact.formula(), x, false);
                let fact = fb.finish(g, self.num_free_vars);
                self.facts.push(Fact{num_boxes:self.boxes.len(), fact});
            } else {
                panic!("forall box is empty");
            }
        } else {
            panic!("Not in a forall box");
        }
    }
}
