use crate::formula::{Formula, FormulaPackage, FormulaReader, FreeVar, Outermost};
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
    Layers(Vec<LayerDetail>),
    Ignore,
}

enum LayerDetail {
    Forall(FormulaPackage),
    Imp(FormulaPackage, FormulaPackage),
}

impl LayerDetail {
    fn formula(&self) -> Formula<'_> {
        match self {
            LayerDetail::Forall(f) => f.formula(),
            LayerDetail::Imp(_, f) => f.formula(),
        }
    }

    fn hypothesis(&self) -> Formula<'_> {
        match self {
            LayerDetail::Forall(_) => panic!("Not an imp"),
            LayerDetail::Imp(h, _) => h.formula(),
        }
    }

    fn num_free_vars(&self) -> u32 {
        match self {
            LayerDetail::Forall(f) => f.num_free_vars(),
            LayerDetail::Imp(_, f) => f.num_free_vars(),
        }
    }

    fn is_imp(&self) -> bool {
        matches!(self, LayerDetail::Imp(_, _))
    }
}

#[derive(Clone, Copy)]
struct AugmentedFormula<'a> {
    formula: Formula<'a>,
    num_free_vars: u32,
    layers: &'a [LayerDetail],
}

struct SpecializationResult {
    hypotheses: Vec<FormulaPackage>,
    specializations: Vec<FormulaPackage>,
}

impl<'a> AugmentedFormula<'a> {
    fn layer(self, i: usize) -> Formula<'a> {
        if i == 0 {
            self.formula
        } else {
            self.layers[i - 1].formula()
        }
    }

    fn layer_free_vars(self, i: usize) -> u32 {
        if i == 0 {
            self.num_free_vars
        } else {
            self.layers[i - 1].num_free_vars()
        }
    }

    fn num_layers(self) -> usize {
        self.layers.len() + 1
    }

    /**
     * Return whether self can be derived from other by specializing variables and proving
     * hypothesis. Basically whether you can get there by unpeeling the "forall" and "imp" layers.
     */
    fn is_specialization_of(
        self,
        g: &Globals,
        other: AugmentedFormula<'_>,
    ) -> Option<SpecializationResult> {
        if self.num_layers() > other.num_layers() {
            return None;
        }
        let i = other.num_layers() - self.num_layers();
        let layer = other.layer(i);
        if let Some(specs) = self.formula.is_specialization_of(
            g,
            layer,
            other.num_free_vars,
            other.layer_free_vars(i) - other.num_free_vars,
        ) {
            let specializations = specs
                .iter()
                .map(|spec| {
                    spec.unwrap_or_else(Formula::dummy)
                        .package(g)
                })
                .collect();
            let hypotheses = other
                .layers
                .iter()
                .filter(|ld| ld.is_imp())
                .map(|ld| ld.hypothesis().package(g))
                .collect();
            Some(SpecializationResult {
                hypotheses,
                specializations,
            })
        } else {
            None
        }
    }
}

fn gen_extra(g: &Globals, f: Formula<'_>, num_free_vars: u32) -> Vec<LayerDetail> {
    let mut result = vec![];
    match f.outermost() {
        Outermost::Forall => {
            let var = FreeVar::new(num_free_vars);
            let fp = FormulaPackage::subst_quantified_var(g, f, FormulaPackage::free_var(var, num_free_vars+1).formula(), false);
            result.push(LayerDetail::Forall(fp));
            let f2 = result[result.len() - 1].formula();
            let rest = gen_extra(g, f2, num_free_vars + 1);
            result.extend(rest);
        }
        Outermost::Rimp => {
            let mut reader = FormulaReader::new(f);
            reader.expect_rimp(g).unwrap();
            let f1 = reader.read_formula(g, num_free_vars);
            let f2 = reader.read_formula(g, num_free_vars);
            reader.end();
            result.push(LayerDetail::Imp(
                f2.package(g),
                f1.package(g),
            ));
            let rest = gen_extra(g, f1, num_free_vars);
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

    fn get_augmented_formula(&self, i: usize) -> Option<AugmentedFormula<'_>> {
        if let Extra::Layers(layers) = &self.extra[i] {
            Some(AugmentedFormula {
                formula: self.pc.formula(i),
                num_free_vars: self.pc.formula_free_vars(i),
                layers,
            })
        } else {
            None
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
