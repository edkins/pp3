use crate::formula::{FormulaPackage, FreeVar, ToFormula};
use crate::globals::{self, GlobalSymbol, Globals};
use crate::script::{Line, Script};
use std::collections::HashMap;

struct Parser<'a> {
    inp: &'a str,
}

#[derive(Debug, Eq, PartialEq)]
#[must_use]
pub enum Token {
    Number(u32),
    Word(Word),
    UndefinedSymbol(String),
    Eof,
    Char(char),
    Arrow,
    Forall,
    Exists,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Word {
    Global(GlobalSymbol),
    FreeVar(FreeVar),
}

#[derive(Debug)]
pub enum ParseError {
    AlreadyDefined,
    BadChar(char),
    ExpectingToken(Token),
    ExpectingEof,
    ExpectingFreshName,
    ExpectingLineSeparator,
    ExpectingTerm,
    ExpectingType,
    JunkAfterNumber(char),
    NumberTooBig,
    TooManyFreeVars,
    TypeMustBeUnary,
    UnexpectedProofElement,
}

struct Context {
    map: HashMap<String, Word>,
    num_free_vars: u32,
}

#[derive(Eq, Ord, PartialEq, PartialOrd)]
enum Tightness {
    Formula,
    Or,
    And,
    Cmp,
    Add,
    Mul,
    Term,
}

enum ParseResult {
    Formula(FormulaPackage),
    Forall(FreeVar, Vec<Line>),
    Imp(FormulaPackage, Vec<Line>),
    Box(Vec<Line>),
    Eof,
    CloseBrace,
}

impl ParseResult {
    fn expect_formula(self) -> FormulaPackage {
        match self {
            ParseResult::Formula(f) => f,
            _ => panic!("Expecting formula"),
        }
    }

    fn into_line(self, _g: &Globals, _ctx: &Context) -> Result<Line, ParseError> {
        match self {
            ParseResult::Formula(f) => Ok(Line::Formula(f)),
            ParseResult::Forall(x, lines) => Ok(Line::Forall(x, Script::new(lines))),
            ParseResult::Imp(hyp, lines) => Ok(Line::Imp(hyp, Script::new(lines))),
            _ => Err(ParseError::UnexpectedProofElement),
        }
    }
}

fn binop(w: &Token) -> Option<(Tightness, GlobalSymbol, Tightness, bool)> {
    match w {
        Token::Arrow => Some((Tightness::Formula, globals::RIMP, Tightness::Formula, true)),
        Token::Char('|') => Some((Tightness::Or, globals::OR, Tightness::And, false)),
        Token::Char('&') => Some((Tightness::And, globals::AND, Tightness::Cmp, false)),
        Token::Char('=') => Some((Tightness::Cmp, globals::EQ, Tightness::Add, false)),
        Token::Char('+') => Some((Tightness::Add, globals::ADD, Tightness::Mul, false)),
        Token::Char('*') => Some((Tightness::Mul, globals::MUL, Tightness::Term, false)),
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
        Context {
            map,
            num_free_vars: 0,
        }
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
        Ok((
            Context {
                map,
                num_free_vars: self.num_free_vars + 1,
            },
            x,
        ))
    }
}

impl<'a> Parser<'a> {
    fn new(inp: &'a str) -> Self {
        Parser { inp }
    }

    fn token(&mut self, ctx: &Context) -> Result<Token, ParseError> {
        loop {
            match self.inp.chars().next() {
                None => return Ok(Token::Eof),
                Some(' ' | '\t' | '\r' | '\n') => self.inp = &self.inp[1..],
                Some(c @ '0'..='9') => {
                    self.inp = &self.inp[1..];
                    let mut n: u32 = (c as u32) - ('0' as u32);
                    loop {
                        match self.inp.chars().next() {
                            Some(c @ '0'..='9') => {
                                n = n
                                    .checked_mul(10)
                                    .and_then(|n| n.checked_add((c as u32) - ('0' as u32)))
                                    .ok_or(ParseError::NumberTooBig)?;
                                self.inp = &self.inp[1..];
                            }
                            Some(c @ ('a'..='z' | 'A'..='Z' | '_')) => {
                                return Err(ParseError::JunkAfterNumber(c))
                            }
                            _ => return Ok(Token::Number(n)),
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
                        _ => return Ok(Token::Char('-')),
                    }
                }
                Some(
                    c @ ('(' | ')' | '{' | '}' | ',' | ':' | ';' | '+' | '*' | '=' | '&' | '|'),
                ) => {
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
                                return match word {
                                    "forall" => Ok(Token::Forall),
                                    "exists" => Ok(Token::Exists),
                                    _ => match ctx.get(word) {
                                        Some(w) => Ok(Token::Word(w)),
                                        None => Ok(Token::UndefinedSymbol(word.to_owned())),
                                    },
                                };
                            }
                        }
                    }
                }
                Some(c) => return Err(ParseError::BadChar(c)),
            }
        }
    }

    fn insist(&mut self, ctx: &Context, t: Token) -> Result<(), ParseError> {
        if self.token(ctx)? == t {
            return Ok(());
        }
        Err(ParseError::ExpectingToken(t))
    }

    fn parse_type(
        &mut self,
        g: &Globals,
        ctx: &Context,
        x: impl ToFormula,
    ) -> Result<FormulaPackage, ParseError> {
        match self.token(ctx)? {
            Token::Word(Word::Global(sym)) => {
                let arity = g.get_arity(sym);
                if arity == 1 {
                    Ok(FormulaPackage::global(g, sym, ctx.num_free_vars, &[x]))
                } else {
                    Err(ParseError::TypeMustBeUnary)
                }
            }
            _ => Err(ParseError::ExpectingType),
        }
    }

    fn parse_term(&mut self, g: &Globals, ctx: &Context) -> Result<FormulaPackage, ParseError> {
        Ok(self.parse_term_or_line(g, ctx, false)?.expect_formula())
    }

    fn parse_term_or_line(
        &mut self,
        g: &Globals,
        ctx: &Context,
        allow_line: bool,
    ) -> Result<ParseResult, ParseError> {
        match self.token(ctx)? {
            Token::Number(n) => Ok(ParseResult::Formula(FormulaPackage::literal_u32(
                n,
                ctx.num_free_vars,
            ))),
            Token::Word(Word::Global(sym)) => {
                let arity = g.get_arity(sym);
                let mut params = Vec::with_capacity(arity as usize);
                if arity != 0 {
                    self.insist(ctx, Token::Char('('))?;
                    for i in 0..arity {
                        let (param, t) = self.parse_formula(g, ctx, Tightness::Formula)?;
                        params.push(param);
                        if i == arity - 1 {
                            if t != Token::Char(')') {
                                return Err(ParseError::ExpectingToken(Token::Char(')')));
                            }
                        } else if t != Token::Char(',') {
                            return Err(ParseError::ExpectingToken(Token::Char(',')));
                        }
                    }
                }
                let fp = FormulaPackage::global(g, sym, ctx.num_free_vars, &params);
                Ok(ParseResult::Formula(fp))
            }
            Token::Word(Word::FreeVar(x)) => {
                let fp = FormulaPackage::free_var(x, ctx.num_free_vars);
                Ok(ParseResult::Formula(fp))
            }
            Token::Char('(') => {
                let (fp, t) = self.parse_formula(g, ctx, Tightness::Formula)?;
                if t != Token::Char(')') {
                    return Err(ParseError::ExpectingToken(Token::Char(')')));
                }
                Ok(ParseResult::Formula(fp))
            }
            Token::Char('{') => {
                if !allow_line {
                    return Err(ParseError::UnexpectedProofElement);
                }
                let (lines, t) = self.parse_script(g, ctx)?;
                if t != Token::Char('}') {
                    return Err(ParseError::ExpectingToken(Token::Char('}')));
                }
                Ok(ParseResult::Box(lines))
            }
            Token::Forall => match self.token(ctx)? {
                Token::UndefinedSymbol(x) => {
                    self.insist(ctx, Token::Char(':'))?;
                    let (ctx2, var) = ctx.with_free_var(x)?;
                    let fp2 = self.parse_type(
                        g,
                        &ctx2,
                        FormulaPackage::free_var(var, ctx2.num_free_vars),
                    )?;
                    match self.parse_term_or_line(g, &ctx2, allow_line)? {
                        ParseResult::Formula(fp3) => Ok(ParseResult::Formula(
                            FormulaPackage::forall(var, FormulaPackage::imp(fp2, fp3)),
                        )),
                        ParseResult::Box(lines) => Ok(ParseResult::Forall(
                            var,
                            vec![Line::Imp(fp2, Script::new(lines))],
                        )),
                        _ => Err(ParseError::UnexpectedProofElement),
                    }
                }
                Token::Word(_) => Err(ParseError::AlreadyDefined),
                _ => Err(ParseError::ExpectingFreshName),
            },
            Token::Exists => match self.token(ctx)? {
                Token::UndefinedSymbol(x) => {
                    self.insist(ctx, Token::Char(':'))?;
                    let (ctx2, var) = ctx.with_free_var(x)?;
                    let fp2 = self.parse_type(
                        g,
                        &ctx2,
                        FormulaPackage::free_var(var, ctx2.num_free_vars),
                    )?;
                    let fp3 = self.parse_term(g, &ctx2)?;

                    Ok(ParseResult::Formula(FormulaPackage::exists(
                        var,
                        FormulaPackage::and(fp2, fp3),
                    )))
                }
                Token::Word(_) => Err(ParseError::AlreadyDefined),
                _ => Err(ParseError::ExpectingFreshName),
            },
            Token::Char('}') => {
                if allow_line {
                    Ok(ParseResult::CloseBrace)
                } else {
                    Err(ParseError::ExpectingTerm)
                }
            }
            Token::Eof => {
                if allow_line {
                    Ok(ParseResult::Eof)
                } else {
                    Err(ParseError::ExpectingTerm)
                }
            }
            _ => Err(ParseError::ExpectingTerm),
        }
    }

    /*
    fn parse_formula_onto(
        &mut self,
        fb: &mut FormulaBuilder,
        g: &Globals,
        ctx: &Context,
        tightness: Tightness,
    ) -> Result<Token, ParseError> {
        let (f, t) = self.parse_formula(g, ctx, tightness)?;
        fb.push_completed_builder(g, &f);
        Ok(t)
    }
    */

    fn parse_formula(
        &mut self,
        g: &Globals,
        ctx: &Context,
        tightness: Tightness,
    ) -> Result<(FormulaPackage, Token), ParseError> {
        let (r, t) = self.parse_formula_or_line(g, ctx, tightness, false)?;
        Ok((
            r.expect_formula(),
            t.expect("Expected next token to be returned"),
        ))
    }

    fn parse_formula_or_line(
        &mut self,
        g: &Globals,
        ctx: &Context,
        tightness: Tightness,
        allow_line: bool,
    ) -> Result<(ParseResult, Option<Token>), ParseError> {
        let r = self.parse_term_or_line(g, ctx, allow_line)?;
        if let ParseResult::Formula(mut fp) = r {
            let mut t = self.token(ctx)?;
            loop {
                match binop(&t) {
                    Some((tt, sym, nextt, reverse)) => {
                        if tt >= tightness {
                            let pair = self.parse_formula_or_line(
                                g,
                                ctx,
                                nextt,
                                allow_line && (t == Token::Arrow),
                            )?;
                            match pair.0 {
                                ParseResult::Formula(f) => {
                                    fp = if reverse {
                                        FormulaPackage::global(g, sym, ctx.num_free_vars, &[f, fp])
                                    } else {
                                        FormulaPackage::global(g, sym, ctx.num_free_vars, &[fp, f])
                                    };
                                    t = pair.1.unwrap();
                                }
                                ParseResult::Box(lines) => {
                                    if allow_line && t == Token::Arrow {
                                        let result = ParseResult::Imp(fp, lines);
                                        return Ok((result, pair.1));
                                    } else {
                                        return Err(ParseError::UnexpectedProofElement);
                                    }
                                }
                                _ => return Err(ParseError::UnexpectedProofElement),
                            }
                        } else {
                            return Ok((ParseResult::Formula(fp), Some(t)));
                        }
                    }
                    None => return Ok((ParseResult::Formula(fp), Some(t))),
                }
            }
        } else {
            Ok((r, None))
        }
    }

    fn parse_entire_formula(
        &mut self,
        g: &Globals,
        ctx: &Context,
    ) -> Result<FormulaPackage, ParseError> {
        let (fp, t) = self.parse_formula(g, ctx, Tightness::Formula)?;
        if t != Token::Eof {
            return Err(ParseError::ExpectingEof);
        }
        Ok(fp)
    }

    fn parse_script(
        &mut self,
        g: &Globals,
        ctx: &Context,
    ) -> Result<(Vec<Line>, Token), ParseError> {
        let mut result = vec![];
        loop {
            let (r, t) = self.parse_formula_or_line(g, ctx, Tightness::Formula, true)?;
            match r {
                ParseResult::Eof => return Ok((result, Token::Eof)),
                ParseResult::CloseBrace => return Ok((result, Token::Char('}'))),
                _ => {
                    result.push(r.into_line(g, ctx)?);
                    match t {
                        None | Some(Token::Char(';')) => {}
                        Some(tok @ (Token::Char('}') | Token::Eof)) => return Ok((result, tok)),
                        _ => return Err(ParseError::ExpectingLineSeparator),
                    }
                }
            }
        }
    }

    fn parse_entire_script(&mut self, g: &Globals, ctx: &Context) -> Result<Script, ParseError> {
        let (f, t) = self.parse_script(g, ctx)?;
        if t == Token::Eof {
            Ok(Script::new(f))
        } else {
            Err(ParseError::ExpectingEof)
        }
    }

    fn context(&self) -> String {
        self.inp
            .get(..8.min(self.inp.len()))
            .unwrap_or("")
            .to_owned()
    }
}

#[derive(Debug)]
pub struct ErrorWithContext {
    #[allow(dead_code)]
    e: ParseError,
    #[allow(dead_code)]
    context: String,
}

pub fn parse(text: &str) -> Result<(Globals, Script), ErrorWithContext> {
    let g = Globals::default();
    let ctx = Context::new(&g);
    let mut parser = Parser::new(text);
    let script = parser
        .parse_entire_script(&g, &ctx)
        .map_err(|e| ErrorWithContext {
            e,
            context: parser.context(),
        })?;
    Ok((g, script))
}

pub fn parse_sentence(g: &Globals, text: &str) -> Result<FormulaPackage, ParseError> {
    let ctx = Context::new(g);
    let mut parser = Parser::new(text);
    parser.parse_entire_formula(g, &ctx)
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
        let mut p = Parser::new("forall x:nat (x=x)");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "@b0.rimp(eq(b0,b0),nat(b0))");
    }

    #[test]
    fn exists() {
        let g = &Globals::default();
        let ctx = &Context::new(g);
        let mut p = Parser::new("exists x:nat (x=x)");
        let f = p.parse_entire_formula(g, ctx).unwrap();
        assert_eq!(f.to_string(g), "#b0.and(nat(b0),eq(b0,b0))");
    }
}
