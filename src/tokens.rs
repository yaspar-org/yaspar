// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # A Tokenizer for SMTLib
//!
//! This module implements a tokenizer for SMTLib scripts. This tokenizer is only meant to be passed
//! to the parser, which uses tokens to generate abstract syntax trees (ASTs). Therefore, this module
//! is not meant to be exposed for external uses.
//!
//! The main object of this module is [Tokenizer], which is an [Iterator] of [Token]s with location
//! information. One major advantage of [Tokenizer] is that it takes any [Iterator] of [char]s, so
//! that when parsing from a large file or a network stream, this tokenizer is more memory efficient
//! than the default tokenizer from `lalrpop`. The fact that [Tokenizer] only operates on an [Iterator]
//! of [char]s allows various underlying implementations, and therefore brings in more flexibilities
//! in actual use cases.

use crate::ast::{GrammarError, KEYWORD_MAP, Keyword};
use crate::position::{Position, Range};
use crate::utils::{binary_to_string, hex_to_string, parse_binary_str, parse_hexadecimal_str};
use crate::{smt_quoted_symbol_to_string, smt_string_to_string};
use dashu::float::DBig;
use dashu::integer::UBig;
use phf::phf_map;
use std::collections::VecDeque;
use std::fmt::Display;
use std::str::FromStr;

#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum Command {
    Assert,
    CheckSat,
    CheckSatAssuming,
    DeclareConst,
    DeclareDatatype,
    DeclareDatatypes,
    DeclareFun,
    DeclareSort,
    DeclareSortParameter,
    DefineConst,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineSort,
    Echo,
    Exit,
    GetAssertions,
    GetAssignment,
    GetInfo,
    GetModel,
    GetOption,
    GetProof,
    GetUnsatAssumptions,
    GetUnsatCore,
    GetValue,
    Pop,
    Push,
    Reset,
    ResetAssertions,
    SetInfo,
    SetLogic,
    SetOption,
}

pub static COMMAND_MAP: phf::Map<&'static str, Command> = phf_map! {
    "assert" => Command::Assert,
    "check-sat" => Command::CheckSat,
    "check-sat-assuming" => Command::CheckSatAssuming,
    "declare-const" => Command::DeclareConst,
    "declare-datatype" => Command::DeclareDatatype,
    "declare-datatypes" => Command::DeclareDatatypes,
    "declare-fun" => Command::DeclareFun,
    "declare-sort" => Command::DeclareSort,
    "declare-sort-parameter" => Command::DeclareSortParameter,
    "define-const" => Command::DefineConst,
    "define-fun" => Command::DefineFun,
    "define-fun-rec" => Command::DefineFunRec,
    "define-funs-rec" => Command::DefineFunsRec,
    "define-sort" => Command::DefineSort,
    "echo" => Command::Echo,
    "exit" => Command::Exit,
    "get-assertions" => Command::GetAssertions,
    "get-assignment" => Command::GetAssignment,
    "get-info" => Command::GetInfo,
    "get-model" => Command::GetModel,
    "get-option" => Command::GetOption,
    "get-proof" => Command::GetProof,
    "get-unsat-assumptions" => Command::GetUnsatAssumptions,
    "get-unsat-core" => Command::GetUnsatCore,
    "get-value" => Command::GetValue,
    "pop" => Command::Pop,
    "push" => Command::Push,
    "reset" => Command::Reset,
    "reset-assertions" => Command::ResetAssertions,
    "set-info" => Command::SetInfo,
    "set-logic" => Command::SetLogic,
    "set-option" => Command::SetOption,
};

impl Display for Command {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Command::Assert => "assert",
            Command::CheckSat => "check-sat",
            Command::CheckSatAssuming => "check-sat-assuming",
            Command::DeclareConst => "declare-const",
            Command::DeclareDatatype => "declare-datatype",
            Command::DeclareDatatypes => "declare-datatypes",
            Command::DeclareFun => "declare-fun",
            Command::DeclareSort => "declare-sort",
            Command::DeclareSortParameter => "declare-sort-parameter",
            Command::DefineConst => "define-const",
            Command::DefineFun => "define-fun",
            Command::DefineFunRec => "define-fun-rec",
            Command::DefineFunsRec => "define-funs-rec",
            Command::DefineSort => "define-sort",
            Command::Echo => "echo",
            Command::Exit => "exit",
            Command::GetAssertions => "get-assertions",
            Command::GetAssignment => "get-assignment",
            Command::GetInfo => "get-info",
            Command::GetModel => "get-model",
            Command::GetOption => "get-option",
            Command::GetProof => "get-proof",
            Command::GetUnsatAssumptions => "get-unsat-assumptions",
            Command::GetUnsatCore => "get-unsat-core",
            Command::GetValue => "get-value",
            Command::Pop => "pop",
            Command::Push => "push",
            Command::Reset => "reset",
            Command::ResetAssertions => "reset-assertions",
            Command::SetInfo => "set-info",
            Command::SetLogic => "set-logic",
            Command::SetOption => "set-option",
        }
        .fmt(f)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Token {
    // Literals
    Numeral(UBig),
    Decimal(DBig),
    Hexadecimal((Vec<u8>, usize)),
    Binary((Vec<u8>, usize)),
    String(String),
    SimpSymbol(String),
    QuotSymbol(String), // unquoted

    // Reserved Words
    RWBinary,
    RWDecimal,
    RWHexadecimal,
    RWNumeral,
    RWString,
    Underscore,
    Exclamation,
    As,
    Let,
    Exists,
    Forall,
    Match,
    Par,
    /// new in 2.7
    Lambda,

    // Special Treatment
    True,
    False,

    // Parentheses
    Lparen,
    Rparen,

    // Keywords
    Keyword(Keyword),

    // Commands
    Command(Command),
}

pub static SPECIAL_SYMBOLS: phf::Map<&'static str, Token> = phf_map! {
    "BINARY" => Token::RWBinary,
    "DECIMAL" => Token::RWDecimal,
    "HEXADECIMAL" => Token::RWHexadecimal,
    "NUMERAL" => Token::RWNumeral,
    "STRING" => Token::RWString,
    "_" => Token::Underscore,
    "!" => Token::Exclamation,
    "as" => Token::As,
    "let" => Token::Let,
    "exists" => Token::Exists,
    "forall" => Token::Forall,
    "match" => Token::Match,
    "par" => Token::Par,
    "true" => Token::True,
    "false" => Token::False,
    "lambda" => Token::Lambda,
};

/// Check whether s is a special symbol that's reserved
/// currently, all special symbols are reserved, except for "true", and "false"
pub fn is_reserved_special_symbol(s: &str) -> bool {
    SPECIAL_SYMBOLS.contains_key(s) && s != "true" && s != "false"
}

impl Display for Token {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Token::Numeral(n) => n.fmt(f),
            Token::Decimal(d) => d.fmt(f),
            Token::Hexadecimal((bs, n)) => write!(f, "#x{}", hex_to_string(bs, *n)),
            Token::Binary((bs, n)) => write!(f, "#b{}", binary_to_string(bs, *n)),
            Token::String(s) => write!(f, "\"{}\"", s.replace("\"", "\"\"")),
            Token::SimpSymbol(s) => s.fmt(f),
            Token::QuotSymbol(s) => write!(f, "|{s}|"),
            Token::RWBinary => "BINARY".fmt(f),
            Token::RWDecimal => "DECIMAL".fmt(f),
            Token::RWHexadecimal => "HEXADECIMAL".fmt(f),
            Token::RWNumeral => "NUMERAL".fmt(f),
            Token::RWString => "STRING".fmt(f),
            Token::Underscore => "_".fmt(f),
            Token::Exclamation => "!".fmt(f),
            Token::As => "as".fmt(f),
            Token::Let => "let".fmt(f),
            Token::Exists => "exists".fmt(f),
            Token::Forall => "forall".fmt(f),
            Token::Match => "match".fmt(f),
            Token::Par => "par".fmt(f),
            Token::True => "true".fmt(f),
            Token::False => "false".fmt(f),
            Token::Lparen => "(".fmt(f),
            Token::Rparen => ")".fmt(f),
            Token::Keyword(kw) => kw.fmt(f),
            Token::Command(c) => c.fmt(f),
            Token::Lambda => "lambda".fmt(f),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct RangedToken {
    tok: Token,
    range: Range,
}

/// The tokenizer object
pub struct Tokenizer<T> {
    /// Iterator
    iter: T,
    /// a buffer for peeking
    buf: VecDeque<char>,
    /// position information
    position: Position,
    /// whether support block comment or not
    handle_block_comment: bool,
}

impl<T> Tokenizer<T> {
    pub fn new(iter: T, handle_block_comment: bool) -> Self {
        Self {
            iter,
            buf: Default::default(),
            position: Default::default(),
            handle_block_comment,
        }
    }
}

pub type TokenizeResult = Result<RangedToken, GrammarError>;

/// Check wheather a character is printable as per SMTLib standard
pub fn is_printable(c: char) -> bool {
    let code = c as u32;
    (32..=126).contains(&code) || 128 <= code
}

/// Check whether a character is simple as per SMTLib standard
pub fn is_simple(c: char) -> bool {
    c.is_ascii_alphanumeric()
        || c == '!'
        || c == '$'
        || c == '%'
        || c == '&'
        || c == '*'
        || c == '+'
        || c == '-'
        || c == '.'
        || c == '/'
        || c == '<'
        || c == '='
        || c == '>'
        || c == '?'
        || c == '@'
        || c == '^'
        || c == '_'
        || c == '~'
}

/// Check whether a character is simple and legal as a start character as per SMTLib standard
pub fn is_simple_start(c: char) -> bool {
    is_simple(c) && !c.is_ascii_digit()
}

/// Check whether a character is a delimiter as per SMTLib standard
pub fn is_delimiter(c: char) -> bool {
    c.is_ascii_whitespace() || c == '(' || c == ')' || c == ';'
}

type TokenizeState = Result<(String, Position), GrammarError>;

impl<T> Tokenizer<T>
where
    T: Iterator<Item = char>,
{
    fn check_if_match(&mut self, s: &str) -> bool {
        while self.buf.len() < s.len() {
            if let Some(c) = self.iter.next() {
                self.buf.push_back(c);
            } else {
                return false;
            }
        }
        self.buf.iter().zip(s.chars()).all(|(a, b)| *a == b)
    }

    fn next_if_match(&mut self, s: &str) -> bool {
        let r = self.check_if_match(s);
        if r {
            // if matches, then we consume all matched chars
            for _ in 0..s.len() {
                self.next_char();
            }
        }
        r
    }

    /// peek the first char in the iterator
    #[inline]
    pub fn peek(&mut self) -> Option<char> {
        self.buf.front().cloned().or_else(|| {
            let c = self.iter.next();
            if let Some(c) = c {
                self.buf.push_back(c);
            }
            c
        })
    }

    #[inline]
    fn consume_buf(&mut self) {
        self.buf.pop_front();
    }

    /// return the current char if exists and move to the next if the predicate is satisfied
    #[inline]
    fn next_with_pred<F>(&mut self, pred: F) -> Option<char>
    where
        F: Fn(char) -> bool,
    {
        let c = self.peek()?;
        if pred(c) {
            self.consume_buf();
            self.position.incr(c);
            Some(c)
        } else {
            None
        }
    }

    /// consume consecutive chars that satisfy `pred`
    #[inline]
    fn ignore_with_pred<F>(&mut self, pred: F)
    where
        F: Fn(char) -> bool,
    {
        while self.next_with_pred(&pred).is_some() {}
    }

    fn ignore_whitespace(&mut self) {
        self.ignore_with_pred(|c| c.is_ascii_whitespace());
    }

    /// consume all chars until it gets out of the comment
    fn ignore_line_comment(&mut self) {
        self.ignore_with_pred(|c| c != '\n');
    }

    /// return true if the forth coming chars are the head of a block comment
    fn lead_with_block_comment_head(&mut self) -> bool {
        self.handle_block_comment && self.next_if_match("#|")
    }

    fn ignore_block_comment(&mut self) {
        loop {
            if self.next_if_match("|#") {
                break;
            }
            self.next_char();
        }
    }

    /// consume all characters that should be ignored, i.e.
    ///
    /// 1. white spaces
    /// 2. comments (block comment as well if configured)
    fn ignore_spaces_and_comments(&mut self) {
        loop {
            self.ignore_whitespace();
            if self.next_with_pred(|c| c == ';').is_some() {
                self.ignore_line_comment();
            } else if self.lead_with_block_comment_head() {
                self.ignore_block_comment();
            } else {
                break;
            }
        }
    }

    /// iterate to the next char if it's not a delimiter
    fn effective_next(&mut self) -> Option<char> {
        if self.handle_block_comment && self.check_if_match("#|") {
            // in this case, we hit a block comment so we stop the token
            None
        } else {
            self.next_with_pred(|c| !is_delimiter(c))
        }
    }

    /// iterate to the next char
    fn next_char(&mut self) -> Option<char> {
        self.next_with_pred(|_| true)
    }

    /// consume the rest of the token; return an error if `pred` is not satisfied
    #[inline]
    fn consume_until_end_with_pred<F>(
        &mut self,
        mut buf: String,
        start: Position,
        pred: F,
    ) -> TokenizeState
    where
        F: Fn(char) -> bool,
    {
        while let Some(c) = self.effective_next() {
            buf.push(c);
            if !pred(c) {
                return Err(self.bad_token_until_delimited(buf, start));
            }
        }
        Ok((buf, start))
    }

    /// put all remainders of the current token to the buffer
    fn next_until_delimited(&mut self, buf: &mut String) {
        while let Some(c) = self.effective_next() {
            buf.push(c);
        }
    }

    /// eagerly consume digits and return when a non-digit is hit.
    ///
    /// this function could return before the end of the token
    fn next_all_digits(&mut self, buf: &mut String) {
        while let Some(c) = self.next_with_pred(|c| c.is_ascii_digit()) {
            buf.push(c);
        }
    }

    /// consume at least one digit until the end of the token; called after seeing 0. or `digits.`
    /// and now expect digits all the way to the end
    fn next_ge1_digits_until_end(&mut self, buf: String, start: Position) -> TokenizeState {
        let len = buf.len();
        let (buf, start) = self.consume_until_end_with_pred(buf, start, |c| c.is_ascii_digit())?;
        if buf.len() == len {
            // no digit at all, but we must consume at least one
            Err(self.bad_token(buf, start))
        } else {
            Ok((buf, start))
        }
    }

    fn next_with_leading0(&mut self, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push('0');
        match self.effective_next() {
            None => Ok(self.return_token(Token::Numeral(UBig::from(0u32)), start)),
            Some(c) => {
                buf.push(c);
                self.next_with_potential_dot(buf, c, start)
            }
        }
    }

    /// invariant: c.is_acsii_digit()
    fn next_with_leading_digit(&mut self, c: char, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push(c);
        self.next_all_digits(&mut buf);
        match self.effective_next() {
            None => Ok(self.return_token(
                Token::Numeral(UBig::from_str(&buf).unwrap()), // unwrap because we know it's safe
                start,
            )),
            Some(c) => {
                buf.push(c);
                // c is not a digit
                self.next_with_potential_dot(buf, c, start)
            }
        }
    }

    fn next_with_potential_dot(&mut self, buf: String, c: char, start: Position) -> TokenizeResult {
        match c {
            '.' => {
                let (buf, start) = self.next_ge1_digits_until_end(buf, start)?;
                Ok(self.return_token(
                    Token::Decimal(DBig::from_str(&buf).unwrap()), // unwrap because we know it's safe
                    start,
                ))
            }
            _ => Err(self.bad_token_until_delimited(buf, start)),
        }
    }

    fn next_with_double_quote(&mut self, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push('"');
        while let Some(c) = self.next_char() {
            buf.push(c);
            if c == '"' {
                if self.next_with_pred(|c| c == '"').is_some() {
                    // escaped double quote
                    buf.push('"');
                } else {
                    // closing quote
                    break;
                }
            } else if !(is_printable(c) || c.is_ascii_whitespace()) {
                // spec only allows chars from above predicates in a string
                return Err(self.bad_token_until_delimited(buf, start));
            }
        }
        if buf.len() == 1 || !buf.ends_with('"') {
            // reject a single double quote, or a string that does not end with a double quote
            Err(self.bad_token_until_delimited(buf, start))
        } else if let Some(c) = self.effective_next() {
            // error if a string has trailing tokens, e.g. "foo"bar
            buf.push(c);
            Err(self.bad_token_until_delimited(buf, start))
        } else {
            // strip off quotes and replace two quotes with a single one.
            let s = smt_string_to_string(&buf);
            Ok(self.return_token(Token::String(s), start))
        }
    }

    fn next_expecting_binary(&mut self, buf: String, start: Position) -> TokenizeResult {
        let len = buf.len();
        let (buf, start) =
            self.consume_until_end_with_pred(buf, start, |c| c == '0' || c == '1')?;
        if buf.len() == len {
            // there should be at least one digit
            Err(self.bad_token(buf, start))
        } else {
            Ok(self.return_token(Token::Binary(parse_binary_str(&buf[2..])), start))
        }
    }

    fn next_expecting_hex(&mut self, buf: String, start: Position) -> TokenizeResult {
        let len = buf.len();
        let (buf, start) =
            self.consume_until_end_with_pred(buf, start, |c| c.is_ascii_hexdigit())?;
        if buf.len() == len {
            // there should be at least one digit
            Err(self.bad_token(buf, start))
        } else {
            Ok(self.return_token(Token::Hexadecimal(parse_hexadecimal_str(&buf[2..])), start))
        }
    }

    fn next_with_sharp(&mut self, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push('#');
        match self.effective_next() {
            None => Err(self.bad_token(buf, start)),
            Some('b') => {
                buf.push('b');
                self.next_expecting_binary(buf, start)
            }
            Some('x') => {
                buf.push('x');
                self.next_expecting_hex(buf, start)
            }
            Some(c) => {
                buf.push(c);
                Err(self.bad_token_until_delimited(buf, start))
            }
        }
    }

    fn next_with_quoted_symbol(&mut self, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push('|');
        while let Some(c) = self.next_char() {
            buf.push(c);
            if !(is_printable(c) || c.is_ascii_whitespace()) {
                // a quoted symbol only accepts printable and white space chars
                return Err(self.bad_token_until_delimited(buf, start));
            }
            if c == '\\' {
                return Err(self.bad_token_until_delimited(buf, start));
            } else if c == '|' {
                break;
            }
        }
        if buf.len() == 1 || !buf.ends_with('|') {
            Err(self.bad_token_until_delimited(buf, start))
        } else if let Some(c) = self.effective_next() {
            // error out for trailing tokens, e.g. |foo|bar
            buf.push(c);
            Err(self.bad_token_until_delimited(buf, start))
        } else {
            let buf = smt_quoted_symbol_to_string(&buf);
            Ok(self.return_symbol(buf, start, false))
        }
    }

    fn next_with_colon(&mut self, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push(':');
        if let Some(c) = self.effective_next() {
            buf.push(c);
            if is_simple_start(c) {
                // a keyword only accepts a simple symbol
                let (buf, start) = self.next_expecting_simple_symbol(buf, start)?;
                if COMMAND_MAP.contains_key(&buf[1..]) || is_reserved_special_symbol(&buf[1..]) {
                    // simple symbols excludes commands and reserved words!
                    Err(self.bad_token(buf, start))
                } else {
                    match KEYWORD_MAP.get(&buf) {
                        None => Ok(self.return_token(
                            Token::Keyword(Keyword::Other(buf[1..].to_string())),
                            start,
                        )),
                        Some(kw) => Ok(self.return_token(Token::Keyword(kw.clone()), start)),
                    }
                }
            } else {
                Err(self.bad_token_until_delimited(buf, start))
            }
        } else {
            Err(self.bad_token(buf, start))
        }
    }

    fn next_expecting_simple_symbol(&mut self, buf: String, start: Position) -> TokenizeState {
        self.consume_until_end_with_pred(buf, start, is_simple)
    }

    /// invariant: is_simple(c)
    fn next_simple_symbol(&mut self, c: char, start: Position) -> TokenizeResult {
        let mut buf = String::new();
        buf.push(c);
        let (buf, start) = self.next_expecting_simple_symbol(buf, start)?;
        Ok(self.return_symbol(buf, start, true))
    }

    /// given a token, we refine it further if it's a command or a special symbol
    fn return_symbol(&self, buf: String, start: Position, is_simp: bool) -> RangedToken {
        match COMMAND_MAP.get(&buf) {
            None => match SPECIAL_SYMBOLS.get(&buf) {
                None => {
                    if is_simp {
                        self.return_token(Token::SimpSymbol(buf), start)
                    } else {
                        self.return_token(Token::QuotSymbol(buf), start)
                    }
                }
                Some(tok) => self.return_token(tok.clone(), start),
            },
            Some(cmd) => self.return_token(Token::Command(*cmd), start),
        }
    }

    /// when we know we have a bad token, we return the full bad token until the delimiter
    fn bad_token_until_delimited(&mut self, mut buf: String, start: Position) -> GrammarError {
        self.next_until_delimited(&mut buf);
        self.bad_token(buf, start)
    }

    /// return an error with a bad token
    fn bad_token(&self, buf: String, start: Position) -> GrammarError {
        GrammarError::TokenizeError {
            buf,
            range: Range {
                start,
                end: self.position,
            },
        }
    }

    /// return a good token with its range
    fn return_token(&self, tok: Token, start: Position) -> RangedToken {
        RangedToken {
            tok,
            range: Range {
                start,
                end: self.position,
            },
        }
    }

    /// return the next token
    pub fn next_token(&mut self) -> Option<TokenizeResult> {
        self.ignore_spaces_and_comments();
        let start = self.position;
        let c = self.next_char()?;
        Some(match c {
            '(' => Ok(self.return_token(Token::Lparen, start)),
            ')' => Ok(self.return_token(Token::Rparen, start)),
            '0' => self.next_with_leading0(start),
            '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9' => {
                self.next_with_leading_digit(c, start)
            }
            '"' => self.next_with_double_quote(start),
            '#' => self.next_with_sharp(start),
            '|' => self.next_with_quoted_symbol(start),
            ':' => self.next_with_colon(start),
            c => {
                if is_simple(c) {
                    // c cannot be a digit
                    self.next_simple_symbol(c, start)
                } else {
                    let mut buf = String::new();
                    buf.push(c);
                    Err(self.bad_token_until_delimited(buf, start))
                }
            }
        })
    }
}

impl<T> Iterator for Tokenizer<T>
where
    T: Iterator<Item = char>,
{
    type Item = Result<(Position, Token, Position), GrammarError>;

    fn next(&mut self) -> Option<Self::Item> {
        self.next_token()
            .map(|r| r.map(|r| (r.range.start, r.tok, r.range.end)))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tokenize(s: &str, block: bool) -> Option<Result<Token, GrammarError>> {
        let mut iter = Tokenizer::new(s.chars(), block);
        iter.next_token().map(|r| r.map(|r| r.tok))
    }

    fn tok_no_block(s: &str) -> Option<Result<Token, GrammarError>> {
        tokenize(s, false)
    }

    fn tok_block(s: &str) -> Option<Result<Token, GrammarError>> {
        tokenize(s, true)
    }

    #[test]
    fn test_tokenize_whitespaces() {
        assert_eq!(tok_no_block("\n\n    \r\r   \t"), None);
    }

    #[test]
    fn test_tokenize_comments() {
        assert_eq!(tok_no_block("; hello world\n\n\n; bar baz"), None);
        assert_eq!(tok_block("#|;hello world\n\n\n bar baz|#"), None);
        assert!(tok_no_block("1#|").unwrap().is_err());
        assert!(tok_block("1#|").unwrap().is_ok());
    }

    #[test]
    fn test_tokenize_lparen() {
        assert_eq!(tok_no_block("; foo bar\n    (").unwrap(), Ok(Token::Lparen))
    }

    #[test]
    fn test_tokenize_rparen() {
        assert_eq!(tok_no_block("; foo bar\n    )").unwrap(), Ok(Token::Rparen))
    }

    #[test]
    fn test_tokenize_numbers() {
        assert_eq!(
            tok_no_block("    ; foo bar\n     0").unwrap(),
            Ok(Token::Numeral(UBig::from(0u8)))
        );
        assert!(tok_no_block("    ; foo bar\n     0.").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     001").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     0123").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     0baz").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     0.1baz").unwrap().is_err());
        assert_eq!(
            Ok(Token::Decimal(DBig::from_str("0.1").unwrap())),
            tok_no_block("    ; foo bar\n     0.1").unwrap(),
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     0.1024").unwrap(),
            Ok(Token::Decimal(DBig::from_str("0.1024").unwrap()))
        );

        assert_eq!(
            tok_no_block("    ; foo bar\n     1").unwrap(),
            Ok(Token::Numeral(UBig::from(1u8)))
        );
        assert!(tok_no_block("    ; foo bar\n     1.").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     12baz").unwrap().is_err());
        assert!(tok_no_block("    ; foo bar\n     1.2baz").unwrap().is_err());
        assert_eq!(
            tok_no_block("    ; foo bar\n     0.0").unwrap(),
            Ok(Token::Decimal(DBig::from_str("0.0").unwrap()))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     100.000").unwrap(),
            Ok(Token::Decimal(DBig::from_str("100.000").unwrap()))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     99.98").unwrap(),
            Ok(Token::Decimal(DBig::from_str("99.98").unwrap()))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     1.2").unwrap(),
            Ok(Token::Decimal(DBig::from_str("1.2").unwrap()))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     10.24").unwrap(),
            Ok(Token::Decimal(DBig::from_str("10.24").unwrap()))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     1024").unwrap(),
            Ok(Token::Numeral(UBig::from(1024u32)))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     1230").unwrap(),
            Ok(Token::Numeral(UBig::from(1230u32)))
        );
        assert_eq!(
            tok_no_block("    ; foo bar\n     1234567890").unwrap(),
            Ok(Token::Numeral(UBig::from(1234567890u32)))
        );
    }

    #[test]
    fn test_tokenize_strings() {
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "" "#
            )
            .unwrap(),
            Ok(Token::String("".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "0" "#
            )
            .unwrap(),
            Ok(Token::String("0".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "abcde" "#
            )
            .unwrap(),
            Ok(Token::String("abcde".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 " ~" "#
            )
            .unwrap(),
            Ok(Token::String(" ~".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "xyz\u{0394}" "#
            )
            .unwrap(),
            Ok(Token::String(r#"xyz\u{0394}"#.into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "∧∨" "#
            )
            .unwrap(),
            Ok(Token::String("∧∨".into()))
        );
        assert_eq!(
            tok_no_block("\"\n\t01234\r\n\t\"").unwrap(),
            Ok(Token::String("\n\t01234\r\n\t".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "baz" "#
            )
            .unwrap(),
            Ok(Token::String("baz".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 """" "#
            )
            .unwrap(),
            Ok(Token::String("\"".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "x""
z" "#
            )
            .unwrap(),
            Ok(Token::String("x\"\nz".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "" "#
            )
            .unwrap(),
            Ok(Token::String("".into()))
        );
        // accept ; in a string
        assert_eq!(
            tok_no_block(
                r#"    ; foo bar
                 "; baz
" "#
            )
            .unwrap(),
            Ok(Token::String("; baz\n".into()))
        );

        // reject a single double quote
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 ""#
            )
            .unwrap()
            .is_err()
        );
        // reject a string without close quote
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 "baz"#
            )
            .unwrap()
            .is_err()
        );
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 a"baz" "#
            )
            .unwrap()
            .is_err()
        );
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 "baz"b "#
            )
            .unwrap()
            .is_err()
        );
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 0"baz" "#
            )
            .unwrap()
            .is_err()
        );
        assert!(
            tok_no_block(
                r#"    ; foo bar
                 "baz"1 "#
            )
            .unwrap()
            .is_err()
        );
    }

    #[test]
    fn test_tokenize_binary() {
        assert_eq!(
            tok_no_block("; foo bar\n    #xA04").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("A04")))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    #x01Ab").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("01Ab")))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    #x61ff").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("61ff")))
        );
        //     assert!(HexadecimalParser::new().parse(wrap_iter("#xABCD").is_ok());
        assert_eq!(
            tok_no_block("#xABCD").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("ABCD")))
        );
        assert_eq!(
            tok_no_block("#x1ab").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("1ab")))
        );
        assert_eq!(
            tok_no_block("#xDeAdBeEf").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("DeAdBeEf")))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    #b001").unwrap(),
            Ok(Token::Binary(parse_binary_str("001")))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    #b101011").unwrap(),
            Ok(Token::Binary(parse_binary_str("101011")))
        );
        assert_eq!(
            tok_no_block("#b01").unwrap(),
            Ok(Token::Binary(parse_binary_str("01")))
        );
        assert_eq!(
            tok_no_block("#b10").unwrap(),
            Ok(Token::Binary(parse_binary_str("10")))
        );
        assert_eq!(
            tok_no_block("#b1111").unwrap(),
            Ok(Token::Binary(parse_binary_str("1111")))
        );
        assert_eq!(
            tok_no_block("#b00000").unwrap(),
            Ok(Token::Binary(parse_binary_str("00000")))
        );

        assert!(tok_block("; foo bar\n    #").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #a").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #x").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b9").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b00a").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b02").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #xg").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #x123z").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #xz").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #,").unwrap().is_err());

        assert_eq!(
            tok_block("; foo bar\n    #xA04").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("A04")))
        );
        assert_eq!(
            tok_block("; foo bar\n    #x01Ab").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("01Ab")))
        );
        assert_eq!(
            tok_block("; foo bar\n    #x61ff").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("61ff")))
        );
        //     assert!(HexadecimalParser::new().parse(wrap_iter("#xABCD").is_ok());
        assert_eq!(
            tok_block("#xABCD").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("ABCD")))
        );
        assert_eq!(
            tok_block("#x1ab").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("1ab")))
        );
        assert_eq!(
            tok_block("#xDeAdBeEf").unwrap(),
            Ok(Token::Hexadecimal(parse_hexadecimal_str("DeAdBeEf")))
        );
        assert_eq!(
            tok_block("; foo bar\n    #b001").unwrap(),
            Ok(Token::Binary(parse_binary_str("001")))
        );
        assert_eq!(
            tok_block("; foo bar\n    #b101011").unwrap(),
            Ok(Token::Binary(parse_binary_str("101011")))
        );
        assert_eq!(
            tok_block("#b01").unwrap(),
            Ok(Token::Binary(parse_binary_str("01")))
        );
        assert_eq!(
            tok_block("#b10").unwrap(),
            Ok(Token::Binary(parse_binary_str("10")))
        );
        assert_eq!(
            tok_block("#b1111").unwrap(),
            Ok(Token::Binary(parse_binary_str("1111")))
        );
        assert_eq!(
            tok_block("#b00000").unwrap(),
            Ok(Token::Binary(parse_binary_str("00000")))
        );

        assert!(tok_block("; foo bar\n    #").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #a").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #x").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b9").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b00a").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #b02").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #xg").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #x123z").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #xz").unwrap().is_err());
        assert!(tok_block("; foo bar\n    #,").unwrap().is_err());
    }

    #[test]
    fn test_tokenize_special_symbols() {
        for (k, v) in COMMAND_MAP.into_iter() {
            assert_eq!(tok_no_block(k).unwrap(), Ok(Token::Command(*v)));
            assert_eq!(
                tok_no_block(&format!("|{k}|")).unwrap(),
                Ok(Token::Command(*v))
            );
        }
        for (k, v) in SPECIAL_SYMBOLS.into_iter() {
            assert_eq!(tok_no_block(k).unwrap(), Ok(v.clone()));
            assert_eq!(tok_no_block(&format!("|{k}|")).unwrap(), Ok(v.clone()));
        }
        assert_eq!(
            tok_no_block("; foo bar\n    baz").unwrap(),
            Ok(Token::SimpSymbol("baz".into()))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    |baz|").unwrap(),
            Ok(Token::QuotSymbol("baz".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"; foo bar
                |baz
zab| "#
            )
            .unwrap(),
            Ok(Token::QuotSymbol("baz\nzab".into()))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    |;comment|").unwrap(),
            Ok(Token::QuotSymbol(";comment".into()))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    |this is a quoted symbol|").unwrap(),
            Ok(Token::QuotSymbol("this is a quoted symbol".into()))
        );
        assert_eq!(
            tok_no_block(
                r#"; foo bar
            |af klj ^*0 asfe2 (&*)&(#^ $ > > >?"']]984|"#
            )
            .unwrap(),
            Ok(Token::QuotSymbol(
                r#"af klj ^*0 asfe2 (&*)&(#^ $ > > >?"']]984"#.into()
            ))
        );
        assert_eq!(
            tok_no_block("; foo bar\n    ||").unwrap(),
            Ok(Token::QuotSymbol("".into()))
        );

        assert!(tok_no_block("; foo bar\n    [").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    ]").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    [baz]").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    |").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    |\\|").unwrap().is_err());
    }

    #[test]
    fn test_tokenize_keyword() {
        for (k, v) in KEYWORD_MAP.into_iter() {
            assert_eq!(tok_no_block(k).unwrap(), Ok(Token::Keyword(v.clone())));
        }
        assert_eq!(
            tok_no_block("; foo bar\n    :baz").unwrap(),
            Ok(Token::Keyword(Keyword::Other("baz".into())))
        );

        assert!(tok_no_block("; foo bar\n    :").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    :|").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    :[").unwrap().is_err());
        assert!(tok_no_block("; foo bar\n    :|baz|").unwrap().is_err());
    }

    #[test]
    fn test_long_decimal() {
        let s = "99999999999999999999999999999999999999999999999999.75662737647363276464646467236266464623646327262667464276746";
        assert!(tok_no_block(s).unwrap().is_ok())
    }
}
