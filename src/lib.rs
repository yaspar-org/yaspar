// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # Yaspar
//!
//! Yaspar is a parsing library strictly following the SMTLib standard.
//!
//! It is composed of two parts:
//! 1. A tokenizer, which can be found in [crate::tokens::Tokenizer]; given an iterator of [char]s,
//!    it tokenizes them into an iterator of SMTLib tokens;
//! 2. A number of parsers, in the form of callbacks; given an implementation of the corresponding
//!    trait, e.g. [crate::action::ParsingAction], a parser in [crate::smtlib2] parses an iteration
//!    of tokens, and callbacks the functions defined in the trait at appropriate timings, or errors
//!    out, if the tokens are grammatically mal-formed.
//!
//! One example of how to use this crate is to see [crate::action::UnitAction]. This object trivially
//! admits all parsing actions, so it accepts and only accepts grammatically well-formed SMT scripts.

use crate::action::UnitAction;
pub use crate::tokens::Tokenizer;
use crate::tokens::{is_simple, is_simple_start};
use lalrpop_util::lalrpop_mod;

pub mod action;
pub mod ast;
pub mod position;
pub mod tokens;
mod utils;

pub use crate::utils::{binary_to_string, hex_to_string};

lalrpop_mod!(pub smtlib2);

/// converts an SMT string into a normal Rust string
pub fn smt_string_to_string(s: &str) -> String {
    s[1..s.len() - 1].replace("\"\"", "\"")
}

/// converts a quoted symbol representation to a string
pub fn smt_quoted_symbol_to_string(s: &str) -> String {
    s[1..s.len() - 1].to_string()
}

/// if s is a symbol, decide whether it is a simple symbol
pub fn is_simple_symbol(s: &str) -> bool {
    s.len() > 1 && is_simple_start(s.chars().next().unwrap()) && s.chars().all(is_simple)
}

/// obtain a tokenizer from a string
pub fn tokenize_str(
    s: &str,
    allow_block_comments: bool,
) -> Tokenizer<impl Iterator<Item = char> + use<'_>> {
    Tokenizer::new(s.chars(), allow_block_comments)
}

pub struct Parser {
    allow_block_comments: bool,
}

impl Parser {
    pub fn new() -> Self {
        Self::with_block_comments(false)
    }

    pub fn with_block_comments(allow_block_comments: bool) -> Self {
        Self {
            allow_block_comments,
        }
    }

    pub fn parse(&self, input: &str) -> Result<(), String> {
        if !self.allow_block_comments && input.contains("#|") {
            return Err(
                "Block comments are not allowed with current parser configuration".to_string(),
            );
        }

        smtlib2::ScriptParser::new()
            .parse(
                &mut UnitAction,
                tokenize_str(input, self.allow_block_comments),
            )
            .map(|_| ())
            .map_err(|e| e.to_string())
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod test {
    use super::smtlib2::{
        AttributeParser, CommandParser, IdentifierParser, KeywordParser, ScriptParser, SortParser,
        SymbolParser, TermParser,
    };
    use super::*;
    use crate::action::UnitAction;
    use std::fs;
    use std::path::PathBuf;

    fn wrap_iter(s: &str) -> Tokenizer<impl Iterator<Item = char> + use<'_>> {
        tokenize_str(s, false)
    }

    #[test]
    fn test_block_comments() {
        assert!(
            Parser::with_block_comments(true)
                .parse(r#"#| two words |# (assert (= 1 1))"#)
                .is_ok()
        );
        assert!(
            Parser::with_block_comments(true)
                .parse(r#"#| comment 1 |# (assert #| comment 2 |# (= 1 1))"#)
                .is_ok()
        );
        assert!(
            Parser::with_block_comments(true)
                .parse(r#"#|\nThis is a\nmultiline\ncomment\n|# (assert (= 1 1))"#)
                .is_ok()
        );
        assert!(
            Parser::with_block_comments(true)
                .parse(r#"#| !@#$%^&*()_+ \n\t\"'.,<>?/ |# (assert (= 1 1))"#)
                .is_ok()
        );
        assert!(
            Parser::default()
                .parse(r#"#| two words |# (assert (= 1 1))"#)
                .is_err()
        );
        assert!(
            Parser::new()
                .parse(r#"#| two words |# (assert (= 1 1))"#)
                .is_err()
        );
    }

    #[test]
    fn test_attribute_parser() {
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":zippy"))
                .is_ok()
        );
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":zippy foo"))
                .is_ok()
        );
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":zippy #b11"))
                .is_ok()
        );
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":pattern ( )"))
                .is_ok()
        );
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":pattern ( abc )"))
                .is_ok()
        );
        assert!(
            AttributeParser::new()
                .parse(&mut UnitAction, wrap_iter(":pattern ( true )"))
                .is_ok()
        );
    }

    #[test]
    fn test_parse_keyword() {
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":xff"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":date"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":a2"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":foo-bar"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":<="))
                .is_ok()
        );
        // Hmm, grammar suggests this isn't legal...
        //assert!(KeywordParser::new().parse(&mut UnitAction, wrap_iter(":56").is_ok());
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":->"))
                .is_ok()
        );
        // true, false, not are simple symbols
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":not"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":true"))
                .is_ok()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":false"))
                .is_ok()
        );

        // error cases
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":|let|"))
                .is_err()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":99%"))
                .is_err()
        );
        // reserved words can't be used
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":match"))
                .is_err()
        );
        assert!(
            KeywordParser::new()
                .parse(&mut UnitAction, wrap_iter(":push"))
                .is_err()
        );
    }

    #[test]
    fn test_parse_symbol() {
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("abc"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("abc123"))
                .is_ok()
        );

        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("+"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("<="))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("x"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("plus"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("**"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("$"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("<"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("sas"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("<adf"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter(">"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("abc77"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("*"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("$s"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("&6"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("."))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("kkk"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter(".8"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("+34"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("-32"))
                .is_ok()
        );

        // Quoted symbols
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("|abc ∧|"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("| this is a quoted symbol |"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter(
                        r#"| so is
this one |"#
                    )
                )
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("||"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("| \" can occur too |"))
                .is_ok()
        );
        assert!(
            SymbolParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("| af klj ^*0 asfe2 (&*)&(#^ $ > > >?\" ']]984|")
                )
                .is_ok()
        );

        // Error cases
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("0abc"))
                .is_err()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("BINARY"))
                .is_err()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("#"))
                .is_err()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("|\\|"))
                .is_err()
        );
        assert!(
            SymbolParser::new()
                .parse(&mut UnitAction, wrap_iter("|||"))
                .is_err()
        );
    }

    #[test]
    fn test_parse_identifier() {
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("xyz"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ xyz 7)"))
                .is_ok()
        );

        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("plus"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("+"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("<="))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("Real"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("|John Brown|"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ vector - add 4 5)"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ BitVec 32)"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ move up )"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ move down )"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ move left )"))
                .is_ok()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ move right )        "))
                .is_ok()
        );

        // Error cases
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("123"))
                .is_err()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ 123)"))
                .is_err()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ xyz)"))
                .is_err()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ blah #AA)"))
                .is_err()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ blah 1.0)"))
                .is_err()
        );
        assert!(
            IdentifierParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ blah #b10)"))
                .is_err()
        );
    }

    #[test]
    fn test_parse_sort() {
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("Int"))
                .is_ok()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("Bool"))
                .is_ok()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("(_ BitVec 3)"))
                .is_ok()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("( List ( Array Int Real ))"))
                .is_ok()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("((_ FixedSizeList 4) Real )"))
                .is_ok()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("( Set (_ Bitvec 3))"))
                .is_ok()
        );

        // Error cases
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("! Int"))
                .is_err()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("(Blah z"))
                .is_err()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("#!"))
                .is_err()
        );
        assert!(
            SortParser::new()
                .parse(&mut UnitAction, wrap_iter("(List)"))
                .is_err()
        );
    }

    #[test]
    fn test_parse_term() {
        // simple
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("99"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("#b01"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("5.1"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("#x7fA"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("xxx"))
                .is_ok()
        );

        // qual
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("( abcd xxx )"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(not b)"))
                .is_ok()
        );

        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(lambda ((x Int)) (and (<= 0 x) (<= x 9)))")
                )
                .is_ok()
        );

        // exists
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("( exists (( p ( List Int )) ( y ( List Int ))) x)")
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(exists ((a Float)) (as x String))")
                )
                .is_ok()
        );

        // forall
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("( forall (( x ( List Int )) ( y ( List Int ))) x)")
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(forall ((a Float)) (as x String))")
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter(
                        r#"( forall (( x ( List Int )) ( y ( List Int )))
(= ( append x y )
( ite (= x ( as nil ( List Int )))
y
( let (( h ( head x )) ( t ( tail x )))
( insert h ( append t y ))))))"#
                    )
                )
                .is_ok()
        );

        // annotated
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! xxx :blah)"))
                .is_ok()
        );

        // Error cases
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! xxx "))
                .is_err()
        );

        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("true"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("false"))
                .is_ok()
        );

        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named bar)"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named |bar|)"))
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named 10)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named 10.1)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named #x0)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named #b0)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! foo :named (baz))"))
                .is_err()
        );

        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(! (> x y) :pattern ((let ((a b)) b)))")
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(! (> x y) :pattern ((let ((a b)) b) x))")
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter(
                        r#"( forall (( x0 A ) ( x1 A ) ( x2 A ))
(! (=> ( and ( r x0 x1 ) ( r x1 x2 )) ( r x0 x2 ))
:pattern (( r x0 x1 ) ( r x1 x2 ))
:pattern (( p x0 a ))
))"#
                    )
                )
                .is_ok()
        );
        assert!(
            TermParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(! (> x y) :pattern (let ((a b)) b))")
                )
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern let)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern foo)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern 10)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern 10.1)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern #x0)"))
                .is_err()
        );
        assert!(
            TermParser::new()
                .parse(&mut UnitAction, wrap_iter("(! (> x y) :pattern #b0)"))
                .is_err()
        );
    }

    #[test]
    fn test_parse_command() {
        assert!(
            CommandParser::new()
                .parse(&mut UnitAction, wrap_iter("(assert (> x y))"))
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(assert (! (> x y) :pattern ((let ((a b)) b))))")
                )
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(&mut UnitAction, wrap_iter("(assert (! (> x y) :named a0))"))
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(set-option :produce-models true)")
                )
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(&mut UnitAction, wrap_iter("(set-option :incremental true)"))
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(&mut UnitAction, wrap_iter("(check-sat-assuming ( x ))"))
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(check-sat-assuming ( (not x) ))")
                )
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(check-sat-assuming ( (not x) y ))")
                )
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(check-sat-assuming ( (= x y) true (not z) ))")
                )
                .is_ok()
        );
        assert!(
            CommandParser::new()
                .parse(
                    &mut UnitAction,
                    wrap_iter("(declare-sort-parameter foobar)")
                )
                .is_ok()
        );

        // Error cases
        assert!(
            CommandParser::new()
                .parse(&mut UnitAction, wrap_iter("(assert (> x y)"))
                .is_err()
        );
    }

    fn get_test_input_paths() -> Vec<PathBuf> {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/resources/smtcomp");
        fs::read_dir(path)
            .unwrap()
            .map(|e| e.unwrap().path())
            .collect()
    }

    #[test]
    fn test_script_parser() {
        for p in get_test_input_paths() {
            println!("parsing {:?}", p);
            let script = fs::read_to_string(p).expect("Could not read test input file");
            assert!(
                ScriptParser::new()
                    .parse(&mut UnitAction, wrap_iter(&script))
                    .is_ok()
            );
        }
    }

    #[test]
    fn test_parse_empty_script() {
        // parsing an empty script returns an empty vector of commands
        let c = ScriptParser::new().parse(&mut UnitAction, wrap_iter(""));
        assert!(c.is_ok_and(|v| v.is_empty()))
    }
}
