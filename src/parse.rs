use crate::formula::{FormulaBuilder, FreeVar};
use crate::globals::{Globals, GlobalSymbol, self};
use std::collections::HashMap;
use std::mem;

struct Parser<'a> {
    inp: &'a str,
}

#[derive(Debug,Eq,PartialEq)]
enum Token {
    Number(u32),
    Word(Word),
    UndefinedSymbol(String),
    Eof,
    Char(char),
    Arrow,
}

#[derive(Clone,Copy,Debug,Eq,PartialEq)]
enum Word {
    Global(GlobalSymbol),
    FreeVar(FreeVar),
}

#[derive(Debug)]
enum ParseError {
    AlreadyDefined,
    BadChar(char),
    ExpectingToken(Token),
    ExpectingEof,
    ExpectingFreshName,
    ExpectingTerm,
    JunkAfterNumber(char),
    NumberTooBig,
    TooManyFreeVars,
}

struct Context {
    map: HashMap<String, Word>,
    num_free_vars: u32,
}

#[derive(Eq,Ord,PartialEq,PartialOrd)]
enum Tightness {
    Formula,
    Or,
    And,
    Cmp,
    Add,
    Mul,
    Term,
}

fn binop(w: &Token) -> Option<(Tightness, GlobalSymbol, Tightness)> {
    match w {
        Token::Arrow => Some((Tightness::Formula, globals::IMP, Tightness::Formula)),
        Token::Char('|') => Some((Tightness::Or, globals::OR, Tightness::And)),
        Token::Char('&') => Some((Tightness::And, globals::AND, Tightness::Cmp)),
        Token::Char('=') => Some((Tightness::Cmp, globals::EQ, Tightness::Add)),
        Token::Char('+') => Some((Tightness::Add, globals::ADD, Tightness::Mul)),
        Token::Char('*') => Some((Tightness::Mul, globals::MUL, Tightness::Term)),
        _ => None,
    }
}

impl Context {
    fn new(g: &Globals) -> Self {
        let mut map = HashMap::new();
        for i in 0..g.count() {
            let sym = g.global(i);
            let name = g.get_name(sym);
            if map.contains_key(name) {
                panic!("Global defined twice");
            }
            map.insert(name.to_owned(), Word::Global(sym));
        }
        Context{ map, num_free_vars: 0 }
    }

    fn get(&self, x: &str) -> Option<Word> {
        self.map.get(x).cloned()
    }

    fn with_free_var(&self, name: String) -> Result<(Self, FreeVar), ParseError> {
        if self.map.contains_key(&name) {
            return Err(ParseError::AlreadyDefined);
        }
        let mut map = self.map.clone();
        if self.num_free_vars > 0xffffff {
            return Err(ParseError::TooManyFreeVars);
        }
        let x = FreeVar::new(self.num_free_vars);
        map.insert(name, Word::FreeVar(x));
        Ok((Context{ map, num_free_vars: self.num_free_vars + 1 }, x))
    }
}

impl<'a> Parser<'a> {
    fn new(inp: &'a str) -> Self {
        Parser{ inp }
    }

    fn token(&mut self, ctx: &Context) -> Result<Token, ParseError> {
        loop {
            match self.inp.chars().next() {
                None => return Ok(Token::Eof),
                Some(' ' | '\t' | '\r' | '\n') => self.inp = &self.inp[1..],
                Some(c @ '0'..='9') => {
                    self.inp = &self.inp[1..];
                    let mut n:u32 = (c as u32) - ('0' as u32);
                    loop {
                        match self.inp.chars().next() {
                            Some(c @ '0'..='9') => {
                                n = n.checked_mul(10).and_then(|n| n.checked_add((c as u32) - ('0' as u32))).ok_or(ParseError::NumberTooBig)?;
                                self.inp = &self.inp[1..];
                            }
                            Some(c @ ('a'..='z' | 'A'..='Z' | '_')) => {
                                return Err(ParseError::JunkAfterNumber(c))
                            }
                            _ => return Ok(Token::Number(n))
                        }
                    }
                }
                Some('-') => {
                    self.inp = &self.inp[1..];
                    match self.inp.chars().next() {
                        Some('>') => {
                            self.inp = &self.inp[1..];
                            return Ok(Token::Arrow);
                        }
                        _ => return Ok(Token::Char('-'))
                    }
                }
                Some(c @ ('(' | ')' | ',' | '@' | '#' | '.' | '+' | '*' | '=' | '&' | '|')) => {
                    self.inp = &self.inp[1..];
                    return Ok(Token::Char(c));
                }
                Some('a'..='z' | 'A'..='Z' | '_') => {
                    let mut len = 1;
                    loop {
                        match self.inp[len..].chars().next() {
                            Some('a'..='z' | 'A'..='Z' | '_' | '0'..='9') => {
                                len += 1;
                            }
                            _ => {
                                let word = &self.inp[..len];
                                self.inp = &self.inp[len..];
                                return match ctx.get(word) {
                                    Some(w) => Ok(Token::Word(w)),
                                    None => Ok(Token::UndefinedSymbol(word.to_owned())),
                                };
                            }
                        }
                    }
                }
                Some(c) => return Err(ParseError::BadChar(c))
            }
        }
    }

    fn insist(&mut self, ctx: &Context, t: Token) -> Result<(), ParseError> {
        if self.token(ctx)? == t {
            return Ok(());
        }
        Err(ParseError::ExpectingToken(t))
    }

    fn parse_term(&mut self, g: &Globals, ctx: &Context) -> Result<FormulaBuilder, ParseError> {
        let mut fb = FormulaBuilder::default();
        match self.token(ctx)? {
            Token::Number(n) => fb.push_literal_u32(g, n),
            Token::Word(Word::Global(sym)) => {
                fb.push_global(g, sym);
                let arity = g.get_arity(sym);
                if arity == 0 {
                    self.insist(ctx, Token::Char('('))?;
                    self.insist(ctx, Token::Char(')'))?;
                } else {
                    self.insist(ctx, Token::Char('('))?;
                    for i in 0..arity {
                        let t = self.parse_formula_onto(&mut fb, g, ctx, Tightness::Formula)?;
                        if i == arity - 1 {
                            if t != Token::Char(')') {
                                return Err(ParseError::ExpectingToken(Token::Char(')')));
                            }
                        } else {
                            if t != Token::Char(',') {
                                return Err(ParseError::ExpectingToken(Token::Char(',')));
                            }
                        }
                    }
                }
            }
            Token::Word(Word::FreeVar(x)) => {
                fb.push_free_var(g, x);
            }
            Token::Char('(') => {
                let t = self.parse_formula_onto(&mut fb, g, ctx, Tightness::Formula)?;
                if t != Token::Char(')') {
                    return Err(ParseError::ExpectingToken(Token::Char(')')));
                }
            }
            Token::Char(c @ ('@' | '#')) => {
                match self.token(ctx)? {
                    Token::UndefinedSymbol(x) => {
                        let existential = c == '#';
                        self.insist(ctx, Token::Char('.'))?;
                        let (ctx2, var) = ctx.with_free_var(x)?;
                        let f = self.parse_term(g, &ctx2)?;
                        fb.quantify_completed_free_var(g, &f, var, existential);
                    }
                    Token::Word(_) => return Err(ParseError::AlreadyDefined),
                    _ => return Err(ParseError::ExpectingFreshName)
                }
            }
            _ => return Err(ParseError::ExpectingTerm)
        }
        Ok(fb)
    }

    fn parse_formula_onto(&mut self, fb: &mut FormulaBuilder, g: &Globals, ctx: &Context, tightness: Tightness) -> Result<Token, ParseError> {
        let (f, t) = self.parse_formula(g, ctx, tightness)?;
        fb.push_completed_builder(g, &f);
        Ok(t)
    }

    fn parse_formula(&mut self, g: &Globals, ctx: &Context, tightness: Tightness) -> Result<(FormulaBuilder, Token), ParseError> {
        let mut fb = self.parse_term(g, ctx)?;
        let mut t = self.token(ctx)?;
        loop {
            match binop(&t) {
                Some((tt,sym,nextt)) => {
                    if tt >= tightness {
                        let mut fb2 = FormulaBuilder::default();
                        mem::swap(&mut fb2, &mut fb);
                        fb.push_global(g, sym);
                        fb.push_completed_builder(g, &fb2 /* used to be called fb */);
                        t = self.parse_formula_onto(&mut fb, g, ctx, nextt)?;
                    } else {
                        return Ok((fb,t));
                    }
                }
                None => return Ok((fb,t))
            }
        }
    }

    fn parse_entire_formula(&mut self, g: &Globals, ctx: &Context) -> Result<FormulaBuilder, ParseError> {
        let mut fb = FormulaBuilder::default();
        let t = self.parse_formula_onto(&mut fb, g, ctx, Tightness::Formula)?;
        if t != Token::Eof {
            return Err(ParseError::ExpectingEof);
        }
        Ok(fb)
    }
}

#[cfg(test)]
mod test {
    use crate::parse::*;

    #[test]
    fn num() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("125125");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "125125");
    }

    #[test]
    fn add() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("2+3");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "add(2,3)");
    }

    #[test]
    fn add_add() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("2+3+4");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "add(add(2,3),4)");
    }

    #[test]
    fn add_mul() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("2+3*4");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "add(2,mul(3,4))");
    }

    #[test]
    fn mul_add() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("2*3+4");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "add(mul(2,3),4)");
    }

    #[test]
    fn add_mul_paren() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("(2+3)*4");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "mul(add(2,3),4)");
    }

    #[test]
    fn mul_add_paren() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("2*(3+4)");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "mul(2,add(3,4))");
    }

    #[test]
    fn func() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("add(123,456)");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "add(123,456)");
    }

    #[test]
    fn var() {
        let g = &Globals::default();
        let ctx = &Context::new(g).with_free_var("x".to_owned()).unwrap().0;
        let mut p = Parser::new("x");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "f0");
    }

    #[test]
    fn forall() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("@x.(x=x)");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "@b0.eq(b0,b0)");
    }
}
