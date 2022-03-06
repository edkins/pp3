use crate::globals::{self, GlobalSymbol, Globals};
use std::fmt;

mod sym {
    use super::*;
    /**
     * The top 8 bits of an item define its kind.
     *
     * e.g.
     *
     * ```
     * match item & HEAD {
     *     LITERAL => {},
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

    pub const MAX_VARNUM: u32 = DETAIL;

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

    #[derive(Clone, Copy, Eq, PartialEq)]
    pub struct Sym(pub u32);

    impl Sym {
        pub const fn literal(n: u32) -> Sym {
            if n > MAX_VARNUM {
                panic!("n too big");
            }
            Sym(LITERAL + n)
        }

        pub fn free_var(var: FreeVar) -> Sym {
            if var.index() > MAX_VARNUM {
                panic!("Free var too big");
            }
            Sym(FREEVAR + var.index())
        }

        pub fn bound_var(n: u32) -> Sym {
            if n > MAX_VARNUM {
                panic!("Bound var too big");
            }
            Sym(BOUNDVAR + n)
        }

        pub fn global(gs: GlobalSymbol) -> Sym {
            if gs.sym() > MAX_VARNUM {
                panic!("global symbol too big");
            }
            Sym(GLOBAL + gs.sym())
        }

        pub fn rimp() -> Sym {
            Sym::global(globals::RIMP)
        }

        pub fn forall() -> Sym {
            Sym(FORALL)
        }

        pub fn exists() -> Sym {
            Sym(EXISTS)
        }

        pub fn quantifier(existential: bool) -> Sym {
            if existential {
                Sym::exists()
            } else {
                Sym::forall()
            }
        }

        pub fn scope_end() -> Sym {
            Sym(SCOPEEND)
        }

        fn kind(self) -> u32 {
            self.0 & KIND
        }

        fn detail(self) -> u32 {
            self.0 & DETAIL
        }

        pub fn arity(self, g: &Globals) -> u32 {
            match self.kind() {
                LITERAL | BOUNDVAR | FREEVAR => 0,
                GLOBAL => g.get_arity(g.global(self.detail())),
                _ => panic!("Cannot get arity of this symbol")
            }
        }

        pub fn get_literal_value(self) -> Option<u32> {
            if self.kind() == LITERAL {
                Some(self.detail())
            } else {
                None
            }
        }

        pub fn get_free_var_num(self) -> Option<u32> {
            if self.kind() == FREEVAR {
                Some(self.detail())
            } else {
                None
            }
        }

        pub fn get_bound_var_num(self) -> Option<u32> {
            if self.kind() == BOUNDVAR {
                Some(self.detail())
            } else {
                None
            }
        }

        pub fn get_global_num(self) -> Option<u32> {
            if self.kind() == GLOBAL {
                Some(self.detail())
            } else {
                None
            }
        }

        pub fn is_forall(self) -> bool {
            self.kind() == FORALL
        }

        pub fn is_quantifier(self) -> bool {
            self.kind() == FORALL || self.kind() == EXISTS
        }

        pub fn is_specific_quantifier(self, existential: bool) -> bool {
            if existential {
                self.kind() == EXISTS
            } else {
                self.kind() == FORALL
            }
        }

        pub fn is_rimp(self) -> bool {
            self.0 == GLOBAL + globals::RIMP.sym()
        }
    }
}

use sym::Sym;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct Formula<'a> {
    slice: &'a [u32],
    num_free_vars: u32,
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
    Rimp,
    Other,
}

const ZERO:Sym = Sym::literal(0);

impl FormulaPackage {
    pub fn dummy(num_free_vars: u32) -> Self {
        FormulaPackage {
            vec: vec![ZERO.0],
            num_free_vars,
        }
    }

    pub fn formula(&self) -> Formula<'_> {
        Formula { slice: &self.vec, num_free_vars: self.num_free_vars }
    }

    pub fn num_free_vars(&self) -> u32 {
        self.num_free_vars
    }

    pub fn to_string(&self, g: &Globals) -> String {
        self.formula().to_string(g)
    }

    pub fn literal_u32(n: u32, num_free_vars: u32) -> Self {
        FormulaPackage {
            vec: vec![Sym::literal(n).0],
            num_free_vars,
        }
    }

    pub fn global_pkgs(g: &Globals, gsym: GlobalSymbol, num_free_vars: u32, params: &[FormulaPackage]) -> Self {
        let sym = Sym::global(gsym);
        if params.len() != sym.arity(g) as usize {
            panic!("Arity mismatch in global");
        }
        let mut vec = vec![];
        vec.push(sym.0);
        for param in params {
            if param.num_free_vars != num_free_vars {
                panic!("Free var count mismatch in global");
            }
            vec.extend_from_slice(&param.vec);
        }
        FormulaPackage {
            vec,
            num_free_vars,
        }
    }

    pub fn global(g: &Globals, gsym: GlobalSymbol, num_free_vars: u32, params: &[Formula<'_>]) -> Self {
        let sym = Sym::global(gsym);
        if params.len() != sym.arity(g) as usize {
            panic!("Arity mismatch in global");
        }
        let mut vec = vec![];
        vec.push(sym.0);
        for param in params {
            if param.num_free_vars != num_free_vars {
                panic!("Free var count mismatch in global");
            }
            vec.extend_from_slice(param.slice);
        }
        FormulaPackage {
            vec,
            num_free_vars,
        }
    }

    pub fn imp(hyp: Formula<'_>, conc: Formula<'_>) -> Self {
        if hyp.num_free_vars != conc.num_free_vars {
            panic!("Free var count mismatch in imp");
        }
        let mut vec = vec![];
        vec.push(Sym::rimp().0);
        vec.extend_from_slice(conc.slice);
        vec.extend_from_slice(hyp.slice);
        FormulaPackage {
            vec,
            num_free_vars: conc.num_free_vars,
        }
    }

    pub fn and(x: Formula<'_>, y: Formula<'_>) -> Self {
        if x.num_free_vars != y.num_free_vars {
            panic!("Free var count mismatch in and");
        }
        let mut vec = vec![];
        vec.push(Sym::global(globals::AND).0);
        vec.extend_from_slice(x.slice);
        vec.extend_from_slice(y.slice);
        FormulaPackage {
            vec,
            num_free_vars: x.num_free_vars,
        }
    }

    pub fn not(x: Formula<'_>) -> Self {
        let mut vec = vec![];
        vec.push(Sym::global(globals::NOT).0);
        vec.extend_from_slice(x.slice);
        FormulaPackage {
            vec,
            num_free_vars: x.num_free_vars,
        }
    }

    pub fn eq(x: Formula<'_>, y: Formula<'_>) -> Self {
        if x.num_free_vars != y.num_free_vars {
            panic!("Free var count mismatch in eq");
        }
        let mut vec = vec![];
        vec.push(Sym::global(globals::EQ).0);
        vec.extend_from_slice(x.slice);
        vec.extend_from_slice(y.slice);
        FormulaPackage {
            vec,
            num_free_vars: x.num_free_vars,
        }
    }

    pub fn free_var(var: FreeVar, num_free_vars: u32) -> Self {
        if var.index() >= num_free_vars {
            panic!("Free var out of range");
        }
        FormulaPackage {
            vec: vec![Sym::free_var(var).0],
            num_free_vars,
        }
    }

    fn quantify(var: FreeVar, f: Formula<'_>, existential: bool) -> Self {
        if var.index() + 1 != f.num_free_vars {
            panic!("Binding the wrong variable in forall");
        }
        let mut vec = vec![];
        let exact = Sym::free_var(var);
        let mut depth = 0;
        vec.push(Sym::quantifier(existential).0);
        for item in f.iter() {
            if item == exact {
                vec.push(Sym::bound_var(depth).0);
            } else {
                if item.is_quantifier() {
                    depth = depth.checked_add(1).expect("Depth should not exceed max");
                } else if item == Sym::scope_end() {
                    if depth == 0 {
                        panic!("Depth should not be 0 here");
                    }
                    depth -= 1;
                }
                vec.push(item.0);
            }
        }
        if depth != 0 {
            panic!("Depth should be 0 here");
        }
        vec.push(Sym::scope_end().0);
        FormulaPackage {
            vec,
            num_free_vars: f.num_free_vars - 1,
        }
    }

    pub fn forall(var: FreeVar, f: Formula<'_>) -> Self {
        FormulaPackage::quantify(var, f, false)
    }

    pub fn exists(var: FreeVar, f: Formula<'_>) -> Self {
        FormulaPackage::quantify(var, f, true)
    }

    pub fn truth(num_free_vars: u32) -> Self {
        FormulaPackage {
            vec: vec![Sym::global(globals::TRUE).0],
            num_free_vars,
        }
    }

    pub fn falsehood(num_free_vars: u32) -> Self {
        FormulaPackage {
            vec: vec![Sym::global(globals::FALSE).0],
            num_free_vars,
        }
    }

    pub fn subst_free_vars(f: Formula<'_>, fs: &[Formula<'_>], num_resulting_free_vars: u32) -> Self {
        if fs.len() > f.num_free_vars as usize {
            panic!("Substituting too many vars");
        }
        for fi in fs {
            if fi.num_free_vars != num_resulting_free_vars {
                panic!("Wrong number of free vars in substituted formula");
            }
        }
        let start_index = f.num_free_vars - (fs.len() as u32);
        let end_index = f.num_free_vars;
        let mut vec = vec![];
        for item in f.iter() {
            if let Some(varnum) = item.get_free_var_num() {
                if varnum >= start_index && varnum < end_index {
                    let i = (varnum - start_index) as usize;
                    vec.extend_from_slice(fs[i].slice);
                } else {
                    vec.push(item.0);
                }
            } else {
                vec.push(item.0);
            }
        }
        FormulaPackage {
            vec,
            num_free_vars: num_resulting_free_vars
        }
    }

    pub fn subst_quantified_var(g: &Globals, f: Formula<'_>, f2: Formula<'_>, existential: bool) -> Self {
        let num_resulting_free_vars = f2.num_free_vars;
        let mut vec = vec![];
        let mut depth = 0;

        if !f.get(0).is_specific_quantifier(existential) {
            panic!("Not correct quantifier");
        }
        for i in 1..f.len()-1 {
            let item = f.get(i);
            if let Some(varnum) = item.get_bound_var_num() {
                if varnum == depth {
                    vec.extend_from_slice(f2.slice);
                } else {
                    vec.push(item.0);
                }
            } else {
                if item.is_quantifier() {
                    depth += 1;
                } else if item == Sym::scope_end() {
                    depth -= 1;
                }
                vec.push(item.0);
            }
        }
        if f.get(f.len()-1) != Sym::scope_end() {
            panic!("No scope end");
        }
        FormulaPackage {
            vec,
            num_free_vars: num_resulting_free_vars
        }
    }
}

impl<'a> Formula<'a> {
    pub fn num_free_vars(self) -> u32 {
        self.num_free_vars
    }

    pub fn iter(self) -> impl Iterator<Item=Sym> + 'a {
        self.slice.iter().map(|n|Sym(*n))
    }

    pub fn len(self) -> usize {
        self.slice.len()
    }

    pub fn get(self, i: usize) -> Sym {
        Sym(self.slice[i])
    }

    pub fn to_string(self, g: &Globals) -> String {
        let mut result = String::new();
        let garbage = slice_to_string(&mut result, self.slice, g, 0);
        if !garbage.is_empty() {
            panic!("Trailing garbage when printing formula");
        }
        result
    }

    pub fn dummy() -> Self {
        Formula {
            slice: &[ZERO.0],
            num_free_vars: 0,
        }
    }

    pub fn package(self, _g: &Globals) -> FormulaPackage {
        let num_free_vars = self.num_free_vars;
        for item in self.iter() {
            if let Some(varnum) = item.get_free_var_num() {
                if varnum >= num_free_vars {
                    panic!("Free variable out of range");
                }
            }
        }
        FormulaPackage {
            vec: self.slice.to_vec(),
            num_free_vars,
        }
    }

    pub fn outermost(self) -> Outermost {
        let first = self.get(0);
        if first.is_forall() {
            Outermost::Forall
        } else if first.is_rimp() {
            Outermost::Rimp
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
        while i < self.len() {
            let item = other.get(j);
            j += 1;
            let fv = item.get_free_var_num();
            if fv.is_some() && fv.unwrap() >= common_free_vars {
                let index = (fv.unwrap() - common_free_vars) as usize;
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
                        num_free_vars: common_free_vars + result_vars,
                    });
                    i += split_len;
                }
            } else {
                if self.get(i) != item {
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
        if var <= sym::MAX_VARNUM {
            FreeVar { var }
        } else {
            panic!("Var out of range");
        }
    }

    pub fn index(self) -> u32 {
        self.var
    }
}

impl fmt::Display for FreeVar {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", freevar_name(self.var))
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
    let sym = Sym(item);
    slice = &slice[1..];
    if let Some(n) = sym.get_literal_value() {
        result.push_str(&format!("{}", n));
        slice
    } else if let Some(v) = sym.get_bound_var_num() {
        result.push_str(&boundvar_name(
            depth.checked_sub(1 + v).expect("Bound var out of range"),
        ));
        slice
    } else if let Some(v) = sym.get_free_var_num() {
        result.push_str(&freevar_name(v));
        slice
    } else if let Some(gnum) = sym.get_global_num() {
        let gsym = g.global(gnum);
        result.push_str(g.get_name(gsym));
        result.push('(');
        for i in 0..sym.arity(g) {
            if i > 0 {
                result.push(',');
            }
            slice = slice_to_string(result, slice, g, depth);
        }
        result.push(')');
        slice
    } else if sym.is_quantifier() {
        result.push(if sym.is_forall() {'@'} else {'#'});
        result.push_str(&boundvar_name(depth));
        result.push('.');
        slice = slice_to_string(result, slice, g, depth + 1);
        if Sym(slice[0]) != Sym::scope_end() {
            panic!("Expecting scope end at this point");
        }
        &slice[1..]
    } else {
        panic!("Unexpected kind: {:x}", item);
    }
}

pub fn first_term_len(g: &Globals, slice: &[u32]) -> usize {
    let item = Sym(slice[0]);
    if item.is_quantifier() {
        2 + first_term_len(g, &slice[1..])
    } else {
        let mut result = 1;
        for _ in 0..item.arity(g) {
            result += first_term_len(g, &slice[result..]);
        }
        result
    }
}

#[derive(Debug)]
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

    fn get(&self, i: usize) -> Sym {
        Sym(self.remainder[i])
    }

    pub fn expect_global(&mut self, g: &Globals, sym: GlobalSymbol) -> Result<(), ReadError> {
        if self.terms_remaining == 0 {
            panic!("No terms remaining in reader");
        }
        let gsym = Sym::global(sym);
        if self.get(0) == gsym {
            self.remainder = &self.remainder[1..];
            self.terms_remaining += gsym.arity(g) - 1;
            Ok(())
        } else {
            Err(ReadError)
        }
    }

    pub fn expect_rimp(&mut self, g: &Globals) -> Result<(), ReadError> {
        self.expect_global(g, globals::RIMP)
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

    pub fn read_formula(&mut self, g: &Globals, num_free_vars: u32) -> Formula<'a> {
        match self.terms_remaining {
            0 => panic!("No terms remaining in reader"),
            1 => {
                self.terms_remaining -= 1;
                let slice = self.remainder;
                self.remainder = &[];
                Formula { slice, num_free_vars }
            }
            _ => {
                let len = first_term_len(g, self.remainder);
                let slice = &self.remainder[..len];
                self.remainder = &self.remainder[len..];
                self.terms_remaining -= 1;
                Formula { slice, num_free_vars }
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
    fn print_literal() {
        let g = &Globals::default();
        let fp = FormulaPackage::literal_u32(42, 0);
        assert_eq!(fp.to_string(g), "42");
    }

    #[test]
    fn print_var0() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::free_var(x, 1);
        assert_eq!(fp.to_string(g), "f0");
    }

    #[test]
    #[should_panic]
    fn pkg_var0_panic() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let _ = FormulaPackage::free_var(x, 0);
    }

    #[test]
    fn print_var0_forall() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::forall(x, FormulaPackage::free_var(x, 1).formula());
        assert_eq!(fp.num_free_vars, 0);
        assert_eq!(fp.to_string(g), "@b0.b0");
    }

    #[test]
    fn print_var0_exists() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::exists(x, FormulaPackage::free_var(x, 1).formula());
        assert_eq!(fp.num_free_vars, 0);
        assert_eq!(fp.to_string(g), "#b0.b0");
    }

    #[test]
    fn print_rimp() {
        let g = &Globals::default();
        let fp = FormulaPackage::imp(FormulaPackage::truth(0).formula(), FormulaPackage::falsehood(0).formula());
        assert_eq!(fp.to_string(g), "rimp(false(),true())");
    }

    #[test]
    #[should_panic]
    fn imp_mismatch() {
        let g = &Globals::default();
        let _ = FormulaPackage::imp(FormulaPackage::truth(0).formula(), FormulaPackage::falsehood(1).formula());
    }

    #[test]
    fn print_and() {
        let g = &Globals::default();
        let fp = FormulaPackage::and(FormulaPackage::truth(0).formula(), FormulaPackage::falsehood(0).formula());
        assert_eq!(fp.to_string(g), "and(true(),false())");
    }

    #[test]
    #[should_panic]
    fn and_mismatch() {
        let g = &Globals::default();
        let _ = FormulaPackage::and(FormulaPackage::truth(0).formula(), FormulaPackage::falsehood(1).formula());
    }

    #[test]
    fn print_not() {
        let g = &Globals::default();
        let fp = FormulaPackage::not(FormulaPackage::falsehood(0).formula());
        assert_eq!(fp.to_string(g), "not(false())");
    }

    #[test]
    fn var0_subst() {
        let g = &Globals::default();
        let x = FreeVar::new(0);

        let fp = FormulaPackage::free_var(x, 1);

        let fp2 = FormulaPackage::literal_u32(3, 0);

        let fp3 = FormulaPackage::subst_free_vars(fp.formula(), &[fp2.formula()], 0);

        assert_eq!(fp3.num_free_vars, 0);
        assert_eq!(fp3.to_string(g), "3");
    }

    #[test]
    fn print_free() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::global_pkgs(g, globals::ADD, 1, &[FormulaPackage::free_var(x, 1), FormulaPackage::literal_u32(1,1)]);
        assert_eq!(fp.to_string(g), "add(f0,1)");
    }

    #[test]
    fn print_exists() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::exists(x,
            FormulaPackage::global_pkgs(g, globals::EQ, 1, &[FormulaPackage::free_var(x, 1), FormulaPackage::literal_u32(37, 1)]).formula());
        assert_eq!(fp.to_string(g), "#b0.eq(b0,37)");
    }

    #[test]
    fn print_forall() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let fp = FormulaPackage::forall(x, FormulaPackage::not(FormulaPackage::free_var(x,1).formula()).formula());
        assert_eq!(fp.to_string(g), "@b0.not(b0)");
    }

    #[test]
    fn print_bound_levels() {
        let g = &Globals::default();
        let x = FreeVar::new(0);
        let y = FreeVar::new(1);

        let fp = FormulaPackage::forall(x,
            FormulaPackage::imp(
                FormulaPackage::exists(y,
                    FormulaPackage::eq(
                        FormulaPackage::free_var(x,2).formula(),
                        FormulaPackage::free_var(y,2).formula(),
                    ).formula(),
                ).formula(),
                FormulaPackage::eq(
                    FormulaPackage::free_var(x,1).formula(),
                    FormulaPackage::free_var(x,1).formula(),
                ).formula(),
            ).formula());
        assert_eq!(
            &fp.to_string(g),
            "@b0.rimp(eq(b0,b0),#b1.eq(b0,b1))"
        );
    }

    #[test]
    fn subst_quantified() {
        let g = &Globals::default();
        let x0 = FreeVar::new(0);
        let x1 = FreeVar::new(1);

        let xyf = FormulaPackage::global_pkgs(&g, globals::ADD, 2, &[FormulaPackage::free_var(x0,2),FormulaPackage::free_var(x1,2)]);
        let allxf = FormulaPackage::forall(x0, FormulaPackage::free_var(x0,1).formula());
        let fp = FormulaPackage::subst_quantified_var(g, allxf.formula(), xyf.formula(), false);
        assert_eq!(fp.num_free_vars(), 2);
        assert_eq!(fp.to_string(g), "add(f0,f1)");
    }

    #[test]
    fn subst_quantified_with_free() {
        let g = &Globals::default();
        let x0 = FreeVar::new(0);
        let x1 = FreeVar::new(1);

        let xyf = FormulaPackage::global_pkgs(&g, globals::ADD, 2, &[FormulaPackage::free_var(x0,2),FormulaPackage::free_var(x1,2)]);
        let ally = FormulaPackage::forall(x1, xyf.formula());
        let fp = FormulaPackage::subst_quantified_var(g, ally.formula(), xyf.formula(), false);
        assert_eq!(fp.num_free_vars(), 2);
        assert_eq!(fp.to_string(g), "add(f0,add(f0,f1))");
    }

    #[test]
    fn subst_quantified_with_bound_simple() {
        let g = &Globals::default();
        let x0 = FreeVar::new(0);
        let x1 = FreeVar::new(1);

        let lit = FormulaPackage::literal_u32(123,0);
        let xyf = FormulaPackage::global_pkgs(&g, globals::ADD, 2, &[FormulaPackage::free_var(x0,2),FormulaPackage::free_var(x1,2)]);
        let allxy = FormulaPackage::forall(x0, FormulaPackage::forall(x1, xyf.formula()).formula());
        let fp = FormulaPackage::subst_quantified_var(g, allxy.formula(), lit.formula(), false);
        assert_eq!(fp.num_free_vars(), 0);
        assert_eq!(fp.to_string(g), "@b0.add(123,b0)");
    }

    #[test]
    fn subst_quantified_with_bound() {
        let g = &Globals::default();
        let x0 = FreeVar::new(0);
        let x1 = FreeVar::new(1);

        let xyf = FormulaPackage::global_pkgs(&g, globals::ADD, 2, &[FormulaPackage::free_var(x0,2),FormulaPackage::free_var(x1,2)]);
        let allxy = FormulaPackage::forall(x0, FormulaPackage::forall(x1, xyf.formula()).formula());
        let fp = FormulaPackage::subst_quantified_var(g, allxy.formula(), xyf.formula(), false);
        assert_eq!(fp.num_free_vars(), 2);
        assert_eq!(fp.to_string(g), "@b0.add(add(f0,f1),b0)");
    }
}
