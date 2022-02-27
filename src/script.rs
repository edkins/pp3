use crate::globals::Globals;
use crate::formula::{FormulaPackage, FreeVar};

pub struct Script {
    lines: Vec<Line>,
}

pub enum Line {
    Formula(FormulaPackage),
    Forall(FreeVar, Script),
    Imp(FormulaPackage, Script),
}

impl Script {
    pub fn new(lines: Vec<Line>) -> Self {
        Script{ lines }
    }

    pub fn print(&self, g: &Globals, depth: usize) {
        let mut spaces = String::new();
        for _ in 0..depth {
            spaces.push_str("  ");
        }
        for line in &self.lines {
            match line {
                Line::Formula(f) => println!("{spaces}{}", f.formula().to_string(g)),
                Line::Forall(x, script) => {
                    println!("{spaces}forall {} {{", x.to_string());
                    script.print(g, depth + 1);
                    println!("{spaces}}}");
                }
                Line::Imp(hyp, script) => {
                    println!("{spaces}{} -> {{", hyp.formula().to_string(g));
                    script.print(g, depth + 1);
                    println!("{spaces}}}");
                }
            }
        }
    }
}
