use crate::globals::{self, GlobalSymbol, Globals};
use std::fmt;

/**
 * The top 8 bits of an item define its kind.
 *
 * e.g.
 *
 * ```
 * match item & HEAD {
 *     PAIR => {},
 *     NUMBER => {},
 *     GLOBAL => {},
 *     _ => {},
 * }
 * ```
 */
const KIND: u32 = 0xff00_0000;

/**
 * The bottom 24 bits of an item define further details, the meaning of which
 * are dependent on the kind.
 */
const DETAIL: u32 = 0x00ff_ffff;

/**
 * An unsigned integer, at most 0x00ffffff
 */
const LITERAL: u32 = 0x0100_0000;

/**
 * A bound variable. The detail defines which it is (where 0 is the innermost variable).
 */
const BOUNDVAR: u32 = 0x0300_0000;

/**
 * A free variable.
 */
const FREEVAR: u32 = 0x0400_0000;

/**
 * A global symbol.
 */
const GLOBAL: u32 = 0x0500_0000;

/**
 * A "forall" block. The detail is always 0.
 */
const FORALL: u32 = 0x0600_0000;

/**
 * An "exists" block. The detail is always 0.
 */
const EXISTS: u32 = 0x0700_0000;

/**
 * The end of a "forall" or "exists" block. The detail is always 0.
 */
const SCOPEEND: u32 = 0x0800_0000;

pub struct FormulaBuilder {
    vec: Vec<u32>,
    terms_remaining: u32,
}

#[derive(Clone, Copy)]
pub struct Formula<'a> {
    slice: &'a [u32],
}

#[derive(Clone)]
pub struct FormulaPackage {
    vec: Vec<u32>,
    num_free_vars: u32,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FreeVar {
    var: u32,
}

pub enum Outermost {
    Forall,
    Imp,
    Other,
}

impl FormulaPackage {
    pub fn formula(&self) -> Formula<'_> {
        Formula { slice: &self.vec }
    }

    pub fn slice(&self) -> &[u32] {
        &self.vec
    }

    pub fn num_free_vars(&self) -> u32 {
        self.num_free_vars
    }
}

impl<'a> Formula<'a> {
    pub fn to_string(self, g: &Globals) -> String {
        let mut result = String::new();
        slice_to_string(&mut result, self.slice, g, 0);
        result
    }

    pub fn dummy() -> Self {
        Formula {
            slice: &[LITERAL], // represents zero
        }
    }

    pub fn package(self, _g: &Globals, num_free_vars: u32) -> FormulaPackage {
        for item in self.slice {
            if item & KIND == FREEVAR && item & DETAIL >= num_free_vars {
                panic!("Free variable out of range");
            }
        }
        FormulaPackage {
            vec: self.slice.to_vec(),
            num_free_vars,
        }
    }

    pub fn outermost(self) -> Outermost {
        let first = self.slice[0];
        if first == FORALL {
            Outermost::Forall
        } else if first == GLOBAL + globals::IMP.sym() {
            Outermost::Imp
        } else {
            Outermost::Other
        }
    }

    /**
     * Check if self is a specialization of other.
     *
     * If so, return a vector of how each free variable is specialized. If not, return None.
     * Some of the variables might be missing, and that's ok, but then we don't know how to
     * specialize them so return None in the corresponding entry.
     *
     * Furthermore, the caller can insist that both formulas have some free variables in common.
     */
    pub fn is_specialization_of(
        self,
        g: &Globals,
        other: Formula<'_>,
        common_free_vars: u32,
        result_vars: u32,
    ) -> Option<Vec<Option<Formula<'a>>>> {
        let mut i = 0;
        let mut j = 0;
        let mut result: Vec<Option<Formula>> = vec![None; result_vars as usize];
        while i < self.slice.len() {
            let item = other.slice[j];
            j += 1;
            if item & KIND == FREEVAR && item & DETAIL >= common_free_vars {
                let index = ((item & DETAIL) - common_free_vars) as usize;
                if let Some(f) = result[index] {
                    // Variable was seen before, so check we encounter the same thing
                    if !self.slice[i..].starts_with(f.slice) {
                        return None;
                    }
                    i += f.slice.len();
                } else {
                    // Variable wasn't seen before, so store what we find
                    let split_len = first_term_len(g, &self.slice[i..]);
                    result[index] = Some(Formula {
                        slice: &self.slice[i..i + split_len],
                    });
                    i += split_len;
                }
            } else {
                if self.slice[i] != item {
                    return None;
                }
                i += 1;
            }
        }
        Some(result)
    }
}

impl FreeVar {
    pub fn new(var: u32) -> Self {
        if var <= DETAIL {
            FreeVar { var }
        } else {
            panic!("Var out of range");
        }
    }

    pub fn index(&self) -> u32 {
        self.var
    }

    fn item(&self) -> u32 {
        FREEVAR | self.var
    }
}

impl fmt::Display for FreeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", freevar_name(self.var))
    }
}

impl Default for FormulaBuilder {
    fn default() -> Self {
        FormulaBuilder {
            vec: vec![],
            terms_remaining: 1,
        }
    }
}

fn boundvar_name(i: u32) -> String {
    format!("b{}", i)
}

fn freevar_name(i: u32) -> String {
    format!("f{}", i)
}

fn slice_to_string<'a>(
    result: &mut String,
    mut slice: &'a [u32],
    g: &Globals,
    depth: u32,
) -> &'a [u32] {
    let item = slice[0];
    let d = item & DETAIL;
    slice = &slice[1..];
    match item & KIND {
        LITERAL => {
            result.push_str(&format!("{}", d));
            slice
        }
        BOUNDVAR => {
            result.push_str(&boundvar_name(
                depth.checked_sub(1 + d).expect("Bound var out of range"),
            ));
            slice
        }
        FREEVAR => {
            result.push_str(&freevar_name(d));
            slice
        }
        GLOBAL => {
            let sym = g.global(d);
            result.push_str(g.get_name(sym));
            result.push('(');
            for i in 0..g.get_arity(sym) {
                if i > 0 {
                    result.push(',');
                }
                slice = slice_to_string(result, slice, g, depth);
            }
            result.push(')');
            slice
        }
        FORALL => {
            result.push('@');
            result.push_str(&boundvar_name(depth));
            result.push('.');
            slice = slice_to_string(result, slice, g, depth + 1);
            if slice[0] != SCOPEEND {
                panic!("Expecting scope end at this point");
            }
            &slice[1..]
        }
        EXISTS => {
            result.push('#');
            result.push_str(&boundvar_name(depth));
            result.push('.');
            slice = slice_to_string(result, slice, g, depth + 1);
            if slice[0] != SCOPEEND {
                panic!("Expecting scope end at this point");
            }
            &slice[1..]
        }
        _ => panic!("Unexpected kind"),
    }
}

impl FormulaBuilder {
    #[cfg(test)]
    pub fn to_string(&self, g: &Globals) -> String {
        if self.terms_remaining != 0 {
            panic!("Terms remaining");
        }
        let mut result = String::new();
        slice_to_string(&mut result, &self.vec, g, 0);
        result
    }

    fn formula(&self) -> Formula<'_> {
        if self.terms_remaining != 0 {
            panic!("Terms remaining");
        }
        Formula { slice: &self.vec }
    }

    pub fn push_formula(&mut self, _g: &Globals, f: Formula<'_>) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        self.vec.extend_from_slice(f.slice);
        self.terms_remaining -= 1;
    }

    pub fn push_completed_builder(&mut self, _g: &Globals, fb: &FormulaBuilder) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        if fb.terms_remaining != 0 {
            panic!("Still terms remaining on pushed formula builder");
        }
        self.vec.extend_from_slice(&fb.vec);
        self.terms_remaining -= 1;
    }

    pub fn push_global(&mut self, g: &Globals, gsym: GlobalSymbol) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        let sym = gsym.sym();
        if sym > DETAIL {
            panic!("Global sym out of range");
        }
        self.vec.push(GLOBAL | sym);
        self.terms_remaining = (self.terms_remaining - 1)
            .checked_add(g.get_arity(gsym))
            .expect("Too many terms remaining");
    }

    pub fn push_literal_u32(&mut self, _g: &Globals, n: u32) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        if n > DETAIL {
            panic!("Literal value out of range");
        }
        self.vec.push(LITERAL | n);
        self.terms_remaining -= 1;
    }

    pub fn push_free_var(&mut self, _g: &Globals, var: FreeVar) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        self.vec.push(var.item());
        self.terms_remaining -= 1;
    }

    pub fn subst_free_var(
        &mut self,
        _g: &Globals,
        f: Formula<'_>,
        var: FreeVar,
        value: Formula<'_>,
    ) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        let exact = var.item();
        for item in f.slice {
            if *item == exact {
                self.vec.extend_from_slice(value.slice);
            } else {
                self.vec.push(*item);
            }
        }
        self.terms_remaining -= 1;
    }

    pub fn subst_quantified_var_with_free_var(
        &mut self,
        g: &Globals,
        f: Formula<'_>,
        value: FreeVar,
        existential: bool,
    ) {
        let mut fb = FormulaBuilder::default();
        fb.push_free_var(g, value);
        self.subst_quantified_var(g, f, fb.formula(), existential);
    }

    pub fn subst_quantified_var(
        &mut self,
        _g: &Globals,
        f: Formula<'_>,
        value: Formula<'_>,
        existential: bool,
    ) {
        if f.slice[0] != (if existential { EXISTS } else { FORALL }) {
            panic!("Does not start with expected quantifier");
        }
        let mut depth = 0;
        for item in &f.slice[1..f.slice.len() - 1] {
            let kind = item & KIND;
            let detail = item & DETAIL;
            if kind == BOUNDVAR && detail == depth {
                self.vec.extend_from_slice(value.slice);
            } else {
                if kind == FORALL || kind == EXISTS {
                    depth += 1;
                    self.vec.push(*item);
                } else if kind == SCOPEEND {
                    if depth == 0 {
                        panic!("Unexpected end of scope");
                    }
                    depth -= 1;
                }
                self.vec.push(*item);
            }
        }
        if depth != 0 {
            panic!("Unexpectedly still in a scope");
        }
    }

    pub fn quantify_free_var(
        &mut self,
        _g: &Globals,
        f: Formula<'_>,
        var: FreeVar,
        existential: bool,
    ) {
        self.quantify_from_slice(f.slice, var, existential)
    }

    pub fn quantify_completed_free_var(
        &mut self,
        _g: &Globals,
        f: &FormulaBuilder,
        var: FreeVar,
        existential: bool,
    ) {
        if f.terms_remaining != 0 {
            panic!("Still terms remaining");
        }
        self.quantify_from_slice(&f.vec, var, existential)
    }

    fn quantify_from_slice(&mut self, slice: &[u32], var: FreeVar, existential: bool) {
        if self.terms_remaining == 0 {
            panic!("No terms remaining");
        }
        let exact = var.item();
        let mut depth = 0;
        if existential {
            self.vec.push(EXISTS);
        } else {
            self.vec.push(FORALL);
        }
        for item in slice {
            if *item == exact {
                self.vec.push(BOUNDVAR | depth);
            } else {
                match item & KIND {
                    FORALL | EXISTS => {
                        depth += 1;
                        if depth > DETAIL {
                            panic!("Too deep");
                        }
                    }
                    SCOPEEND => {
                        if depth == 0 {
                            panic!("Mismatched scope end");
                        }
                        depth -= 1;
                    }
                    _ => {}
                }
                self.vec.push(*item);
            }
        }
        if depth != 0 {
            panic!("Missing scope end");
        }
        self.vec.push(SCOPEEND);
        self.terms_remaining -= 1;
    }

    pub fn finish(self, _g: &Globals, num_free_vars: u32) -> FormulaPackage {
        if self.terms_remaining != 0 {
            panic!("Still remaining terms");
        }
        for item in &self.vec {
            if item & KIND == FREEVAR && item & DETAIL >= num_free_vars {
                panic!("Free variable out of range");
            }
        }
        FormulaPackage {
            vec: self.vec,
            num_free_vars,
        }
    }
}

pub fn first_term_len(g: &Globals, slice: &[u32]) -> usize {
    let item = slice[0];
    let d = item & DETAIL;
    match item & KIND {
        LITERAL | BOUNDVAR | FREEVAR => 1,
        GLOBAL => {
            let sym = g.global(d);
            let mut result = 1;
            for _ in 0..g.get_arity(sym) {
                result += first_term_len(g, &slice[result..]);
            }
            result
        }
        FORALL | EXISTS => 1 + first_term_len(g, &slice[1..]),
        _ => panic!("Unexpected kind"),
    }
}

pub struct FormulaReader<'a> {
    remainder: &'a [u32],
    terms_remaining: u32,
}

#[derive(Debug)]
pub struct ReadError;

impl<'a> FormulaReader<'a> {
    pub fn new(f: Formula<'a>) -> Self {
        FormulaReader {
            remainder: f.slice,
            terms_remaining: 1,
        }
    }

    pub fn expect_global(&mut self, g: &Globals, sym: GlobalSymbol) -> Result<(), ReadError> {
        if self.terms_remaining == 0 {
            panic!("No terms remaining in reader");
        }
        if self.remainder[0] == GLOBAL + sym.sym() {
            self.remainder = &self.remainder[1..];
            self.terms_remaining += g.get_arity(sym) - 1;
            Ok(())
        } else {
            Err(ReadError)
        }
    }

    pub fn expect_imp(&mut self, g: &Globals) -> Result<(), ReadError> {
        self.expect_global(g, globals::IMP)
    }

    pub fn expect_formula(&mut self, _g: &Globals, f: Formula<'_>) -> Result<(), ReadError> {
        if self.terms_remaining == 0 {
            panic!("No terms remaining in reader");
        }
        let expected_slice = f.slice;
        let len = expected_slice.len();
        if self.remainder.len() >= len && &self.remainder[..len] == expected_slice {
            self.remainder = &self.remainder[len..];
            self.terms_remaining -= 1;
            Ok(())
        } else {
            Err(ReadError)
        }
    }

    pub fn read_formula(&mut self, g: &Globals) -> Formula<'a> {
        match self.terms_remaining {
            0 => panic!("No terms remaining in reader"),
            1 => {
                self.terms_remaining -= 1;
                let slice = self.remainder;
                self.remainder = &[];
                Formula { slice }
            }
            _ => {
                let len = first_term_len(g, self.remainder);
                let slice = &self.remainder[..len];
                self.remainder = &self.remainder[len..];
                self.terms_remaining -= 1;
                Formula { slice }
            }
        }
    }

    pub fn end(self) {
        if self.terms_remaining != 0 {
            panic!("Still terms remaining in reader");
        }
        if !self.remainder.is_empty() {
            panic!("Still data remaining in reader");
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::formula::*;
    use crate::globals;

    #[test]
    fn pkg_literal() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_literal_u32(g, 42);
        fb.finish(g, 0);
    }

    #[test]
    fn pkg_var0() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_free_var(g, x);
        fb.finish(g, 1);
    }

    #[test]
    #[should_panic]
    fn pkg_var0_panic() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_free_var(g, x);
        fb.finish(g, 0);
    }

    #[test]
    #[should_panic]
    fn pkg_unfinished() {
        let fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.finish(g, 0);
    }

    #[test]
    fn var0_forall() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_free_var(g, x);
        let pkg = fb.finish(g, 1);

        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg.formula(), x, false);
        fb.finish(g, 0);
    }

    #[test]
    fn var0_exists() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_free_var(g, x);
        let pkg = fb.finish(g, 1);

        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg.formula(), x, true);
        fb.finish(g, 0);
    }

    #[test]
    fn push_f() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_literal_u32(g, 42);
        let pkg = fb.finish(g, 0);

        let mut fb = FormulaBuilder::default();
        fb.push_formula(g, pkg.formula());
        fb.finish(g, 0);
    }

    #[test]
    fn push_imp() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_global(g, globals::IMP);
        fb.push_global(g, globals::FALSE);
        fb.push_global(g, globals::TRUE);
        fb.finish(g, 0);
    }

    #[test]
    #[should_panic]
    fn push_imp_unfinished() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_global(g, globals::IMP);
        fb.push_global(g, globals::FALSE);
        fb.finish(g, 0);
    }

    #[test]
    fn push_not() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_global(g, globals::NOT);
        fb.push_global(g, globals::FALSE);
        fb.finish(g, 0);
    }

    #[test]
    fn var0_subst() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_free_var(g, x);
        let pkg = fb.finish(g, 1);

        let mut fb = FormulaBuilder::default();
        fb.push_literal_u32(g, 3);
        let pkg_lit = fb.finish(g, 0);

        let mut fb = FormulaBuilder::default();
        fb.subst_free_var(g, pkg.formula(), x, pkg_lit.formula());
        fb.finish(g, 0);
    }

    #[test]
    fn print_n() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        fb.push_literal_u32(g, 123);
        let pkg = fb.finish(g, 0);
        assert_eq!(&pkg.formula().to_string(g), "123");
    }

    #[test]
    fn print_free() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_global(g, globals::ADD);
        fb.push_free_var(g, x);
        fb.push_literal_u32(g, 1);
        let pkg = fb.finish(g, 1);
        assert_eq!(&pkg.formula().to_string(g), "add(f0,1)");
    }

    #[test]
    fn print_exists() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_global(g, globals::EQ);
        fb.push_free_var(g, x);
        fb.push_literal_u32(&g, 37);
        let pkg = fb.finish(g, 1);
        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg.formula(), x, true);
        let pkg2 = fb.finish(g, 0);
        assert_eq!(&pkg2.formula().to_string(g), "#b0.eq(b0,37)");
    }

    #[test]
    fn print_forall() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        fb.push_global(g, globals::NOT);
        fb.push_free_var(g, x);
        let pkg = fb.finish(g, 1);
        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg.formula(), x, false);
        let pkg2 = fb.finish(g, 0);
        assert_eq!(&pkg2.formula().to_string(g), "@b0.not(b0)");
    }

    #[test]
    fn print_bound_levels() {
        let mut fb = FormulaBuilder::default();
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let y = FreeVar::new(1);
        fb.push_global(g, globals::EQ);
        fb.push_free_var(g, x);
        fb.push_free_var(g, y);
        let pkg0 = fb.finish(g, 2);
        println!("{}", pkg0.formula().to_string(g));

        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg0.formula(), y, true);
        let pkg1 = fb.finish(g, 1);
        println!("{}", pkg1.formula().to_string(g));

        let mut fb = FormulaBuilder::default();
        fb.push_global(g, globals::IMP);
        fb.push_global(g, globals::EQ);
        fb.push_free_var(g, x);
        fb.push_free_var(g, x);
        fb.push_formula(g, pkg1.formula());
        let pkg2 = fb.finish(g, 1);
        println!("{}", pkg2.formula().to_string(g));

        let mut fb = FormulaBuilder::default();
        fb.quantify_free_var(g, pkg2.formula(), x, false);
        let pkg = fb.finish(g, 0);
        assert_eq!(
            &pkg.formula().to_string(g),
            "@b0.imp(eq(b0,b0),#b1.eq(b0,b1))"
        );
    }
}
