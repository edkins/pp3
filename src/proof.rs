use crate::axioms;
use crate::formula::{Formula, FormulaPackage, FormulaReader, FreeVar};
use crate::globals::Globals;

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

impl ProofContext {
    pub fn new(g: &Globals) -> Self {
        let facts = axioms::axioms(g)
            .into_iter()
            .map(|fact| {
                if fact.num_free_vars() > 0 {
                    panic!("Not expecting free vars in axiom");
                }
                Fact { num_boxes: 0, fact }
            })
            .collect();
        ProofContext {
            boxes: vec![],
            facts,
            num_free_vars: 0,
        }
    }

    pub fn num_formulas(&self) -> usize {
        self.facts.len()
    }

    pub fn formula(&self, i: usize) -> Formula<'_> {
        self.facts[i].fact.formula()
    }

    pub fn formula_free_vars(&self, i: usize) -> u32 {
        self.facts[i].fact.num_free_vars()
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
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact: hyp.clone(),
        });
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
                while let Some(f) = self.facts.pop() {
                    if f.num_boxes <= self.boxes.len() {
                        self.facts.push(f); // oops didn't mean to remove that one, put it back
                        break;
                    }
                }
                let fact = FormulaPackage::imp(h.formula(), conclusion.fact.formula());
                self.facts.push(Fact {
                    num_boxes: self.boxes.len(),
                    fact,
                });
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
                while let Some(f) = self.facts.pop() {
                    if f.num_boxes <= self.boxes.len() {
                        self.facts.push(f); // oops didn't mean to remove that one, put it back
                        break;
                    }
                }
                self.num_free_vars -= 1;
                let fact = FormulaPackage::forall(x, conclusion.fact.formula());
                self.facts.push(Fact {
                    num_boxes: self.boxes.len(),
                    fact,
                });
            } else {
                panic!("forall box is empty");
            }
        } else {
            panic!("Not in a forall box");
        }
    }

    fn push_fp(&mut self, g: &Globals, fact: FormulaPackage) {
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact,
        });
    }

    pub fn imp_elim(&mut self, g: &Globals, i: usize, j: usize) {
        let mut reader = FormulaReader::new(self.facts[i].fact.formula());
        let num_free_vars = self.facts[i].fact.num_free_vars();
        let hyp = self.facts[j].fact.formula();
        reader.expect_rimp(g).expect("Expecting rimp");
        let conc = reader.read_formula(g, num_free_vars);
        reader.expect_formula(g, hyp).expect("Hyp mismatch");
        reader.end();
        let fact = conc.package(g);
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact,
        });
    }

    pub fn forall_elim(&mut self, g: &Globals, i: usize, value: &FormulaPackage) {
        if value.num_free_vars() > self.num_free_vars {
            panic!("Too many free vars in value");
        }
        let fp = FormulaPackage::subst_quantified_var(g, self.facts[i].fact.formula(), value.formula(), false);
        self.push_fp(g, fp);
    }
}
