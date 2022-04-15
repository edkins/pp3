use crate::axioms;
use crate::formula::{Formula, FormulaPackage, FormulaReader, ToFormula};
use crate::globals::{self, Globals};

pub struct ProofContext {
    boxes: Vec<ProofBox>,
    facts: Vec<Fact>,
    num_free_vars: u32,
}

pub enum ProofBox {
    Forall(u32),
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

    pub fn prev_conclusion(&self, i: usize) -> Formula<'_> {
        if !self.boxes.is_empty() {
            panic!("No conclusion while still boxes");
        }
        self.facts[i].fact.formula()
    }

    pub fn conclusion(&self) -> Formula<'_> {
        self.prev_conclusion(self.facts.len() - 1)
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
                    ProofBox::Imp(h) => println!("assume {}", h.to_string(g)),
                }
                num_boxes_printed += 1;
            }
            println!("   {}", fact.fact.to_string(g));
        }
        println!(">>>>");
    }

    pub fn num_free_vars(&self) -> u32 {
        self.num_free_vars
    }

    pub fn begin_imp_box(&mut self, g: &Globals, hyp: Formula<'_>) -> usize {
        if hyp.num_free_vars() > self.num_free_vars {
            panic!("Too many free vars in hypothesis");
        }
        self.boxes.push(ProofBox::Imp(hyp.package(g)));
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact: hyp.package(g),
        });
        self.facts.len() - 1
    }

    pub fn begin_forall_box(&mut self, _g: &Globals) {
        self.boxes.push(ProofBox::Forall(self.num_free_vars));
        self.num_free_vars += 1;
    }

    pub fn end_imp_box(&mut self, _g: &Globals) -> usize {
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
                let fact = FormulaPackage::imp(self.num_free_vars, h, conclusion.fact);
                self.facts.push(Fact {
                    num_boxes: self.boxes.len(),
                    fact,
                });
                self.facts.len() - 1
            } else {
                panic!("imp box is empty");
            }
        } else {
            panic!("Not in an imp box");
        }
    }

    pub fn end_forall_box(&mut self, _g: &Globals) -> usize {
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
                let fact = FormulaPackage::forall(x, conclusion.fact);
                self.facts.push(Fact {
                    num_boxes: self.boxes.len(),
                    fact,
                });
                self.facts.len() - 1
            } else {
                panic!("forall box is empty");
            }
        } else {
            panic!("Not in a forall box");
        }
    }

    fn push_fp(&mut self, _g: &Globals, fact: FormulaPackage) -> usize {
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact,
        });
        self.facts.len() - 1
    }

    pub fn imp_elim(&mut self, g: &Globals, i: usize, j: usize) -> usize {
        let mut reader = FormulaReader::new(self.facts[i].fact.formula());
        let num_free_vars = self.facts[i].fact.num_free_vars();
        let hyp = &self.facts[j].fact;
        reader.expect_rimp(g).expect("Expecting rimp");
        let conc = reader.read_formula(g, num_free_vars);
        println!("conc: {}", conc.to_string(g));
        reader.expect_formula(g, hyp).expect("Hyp mismatch");
        reader.end();
        let fact = conc.package(g);
        self.facts.push(Fact {
            num_boxes: self.boxes.len(),
            fact,
        });
        self.facts.len() - 1
    }

    pub fn forall_elim(&mut self, g: &Globals, i: usize, value: impl ToFormula) -> usize {
        if value.num_free_vars() > self.num_free_vars {
            panic!("Too many free vars in value");
        }
        let fp = FormulaPackage::subst_quantified_var(g, &self.facts[i].fact, value, false);
        self.push_fp(g, fp)
    }

    pub fn nat_literal_u32(&mut self, g: &Globals, n: u32) -> usize {
        let fp = FormulaPackage::global(
            g,
            globals::NAT,
            self.num_free_vars,
            &[FormulaPackage::literal_u32(n, self.num_free_vars)],
        );
        self.push_fp(g, fp)
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use axioms;

    #[test]
    fn nat_literal() {
        let g = &Globals::default();
        let mut pc = ProofContext::new(g);
        pc.nat_literal_u32(g, 123);
        assert_eq!(pc.conclusion().to_string(g), "nat(123)");
    }

    #[test]
    fn specialize_axiom() {
        let g = &Globals::default();
        let mut pc = ProofContext::new(g);
        let i0 = pc.forall_elim(g, axioms::ADD_0_R, FormulaPackage::literal_u32(3, 0));
        let i1 = pc.nat_literal_u32(g, 3);
        let _ = pc.imp_elim(g, i0, i1);
        assert_eq!(pc.conclusion().to_string(g), "eq(add(3,0),3)");
    }

    #[test]
    fn swap_vars() {
        let g = &Globals::default();
        let mut pc = ProofContext::new(g);
        assert_eq!(
            pc.prev_conclusion(axioms::ADD_SUCC_R).to_string(g),
            "@b0.rimp(@b1.rimp(eq(add(b0,add(b1,1)),add(add(b0,b1),1)),nat(b1)),nat(b0))"
        );
        let xfp = FormulaPackage::free_var(0, 1);
        pc.begin_forall_box(g);
        let xnat = pc.begin_imp_box(
            &g,
            FormulaPackage::global(&g, globals::NAT, 1, &[xfp]).formula(),
        );

        let yfp = FormulaPackage::free_var(1, 2);
        let xfp2 = FormulaPackage::free_var(0, 2);
        pc.begin_forall_box(g);
        let ynat = pc.begin_imp_box(
            g,
            FormulaPackage::global(&g, globals::NAT, 2, &[&yfp]).formula(),
        );

        let spec0 = pc.forall_elim(g, axioms::ADD_SUCC_R, yfp);
        let spec1 = pc.imp_elim(g, spec0, ynat);
        let spec2 = pc.forall_elim(g, spec1, xfp2);
        pc.imp_elim(g, spec2, xnat);
        pc.end_imp_box(g);
        pc.end_forall_box(g);
        pc.end_imp_box(g);
        pc.end_forall_box(g);
        assert_eq!(
            pc.conclusion().to_string(g),
            "@b0.rimp(@b1.rimp(eq(add(b1,add(b0,1)),add(add(b1,b0),1)),nat(b1)),nat(b0))"
        );
    }
}
