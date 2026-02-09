// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

use crate::ast::{DatatypeDec, DatatypeDef, FunctionDef, GrammarError, Keyword, SortDec};
use crate::position::{Position, Range};
use crate::tokens::Token;
use dashu::float::DBig;
use dashu::integer::UBig;
use lalrpop_util::ParseError;
use num_traits::cast::ToPrimitive;
use serde::{Deserialize, Serialize};

pub type ParsingResult<T> = Result<T, ParseError<Position, Token, GrammarError>>;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Pattern<S> {
    Single(Option<S>),
    Applied { head: S, tail: Vec<Option<S>> },
}

/// This function combines mutual datatype declarations into their individual declarations
#[allow(clippy::type_complexity)]
pub(crate) fn sanitize_declare_datatypes<Str, S>(
    range: Range,
    sort_decs: Vec<SortDec<Str>>,
    datatype_decs: Vec<DatatypeDec<Str, S>>,
) -> ParsingResult<(Range, Vec<DatatypeDef<Str, S>>)> {
    if sort_decs.len() != datatype_decs.len() {
        Err(ParseError::User {
            error: GrammarError::DatatypeDeclarationError {
                range,
                num_datatypes: sort_decs.len(),
                num_defs: datatype_decs.len(),
            },
        })
    } else {
        let mut defs = vec![];
        for (d, dec) in sort_decs.into_iter().zip(datatype_decs) {
            let arity = match d.1.to_usize() {
                None => {
                    return Err(ParseError::User {
                        error: GrammarError::Other {
                            range,
                            message: format!("arity {} is too large!", d.1),
                        },
                    });
                }
                Some(n) => n,
            };
            if arity != dec.params.len() {
                return Err(ParseError::User {
                    error: GrammarError::Other {
                        range,
                        message: format!(
                            "arity {arity} does not match the length of the list of parameters {}!",
                            dec.params.len()
                        ),
                    },
                });
            }
            defs.push(DatatypeDef { name: d.0, dec });
        }

        Ok((range, defs))
    }
}

/// This function combines mutual recursive function definitions into their individual definitions
#[allow(clippy::type_complexity)]
pub(crate) fn sanitize_define_funs_rec<Str, S, T>(
    range: Range,
    funs: Vec<(Str, Vec<(Str, S)>, S)>,
    ts: Vec<T>,
) -> ParsingResult<(Range, Vec<FunctionDef<Str, S, T>>)> {
    if funs.len() != ts.len() {
        Err(ParseError::User {
            error: GrammarError::RecFunsDefinitionError {
                range,
                num_funs: funs.len(),
                num_bodies: ts.len(),
            },
        })
    } else {
        Ok((
            range,
            funs.into_iter()
                .zip(ts)
                .map(|((name, vars, out_sort), body)| FunctionDef {
                    name,
                    vars,
                    out_sort,
                    body,
                })
                .collect(),
        ))
    }
}

// now we list a set of callback traits

pub trait ActionOnString {
    type Str;

    fn on_string(&mut self, range: Range, s: String) -> ParsingResult<Self::Str>;
}

pub trait ActionOnConstant: ActionOnString {
    type Constant;

    /// bytes: `little-endian decoding of bytes`, len: `length of the original binary string`
    ///
    /// invariant: the length must be at least the number of bits to encode the bytes
    fn on_constant_binary(
        &mut self,
        range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant>;
    /// bytes: `little-endian decoding of bytes`, len: `length of the original binary string`
    ///
    /// invariant: the length must be at least the length of the shortest encoded string
    fn on_constant_hexadecimal(
        &mut self,
        range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Constant>;
    fn on_constant_decimal(&mut self, range: Range, decimal: DBig)
    -> ParsingResult<Self::Constant>;
    fn on_constant_numeral(&mut self, range: Range, numeral: UBig)
    -> ParsingResult<Self::Constant>;
    fn on_constant_string(
        &mut self,
        range: Range,
        string: Self::Str,
    ) -> ParsingResult<Self::Constant>;
    fn on_constant_bool(&mut self, range: Range, boolean: bool) -> ParsingResult<Self::Constant>;
}

pub trait ActionOnIndex: ActionOnString {
    type Index;

    fn on_index_numeral(&mut self, range: Range, index: UBig) -> ParsingResult<Self::Index>;
    fn on_index_symbol(&mut self, range: Range, index: Self::Str) -> ParsingResult<Self::Index>;
    /// c.f. [ActionOnConstant::on_constant_hexadecimal]
    fn on_index_hexadecimal(
        &mut self,
        range: Range,
        bytes: Vec<u8>,
        len: usize,
    ) -> ParsingResult<Self::Index>;
}

pub trait ActionOnIdentifier: ActionOnIndex {
    type Identifier;

    fn on_identifier(
        &mut self,
        range: Range,
        symbol: Self::Str,
        indices: Vec<Self::Index>,
    ) -> ParsingResult<Self::Identifier>;
}

pub trait ActionOnAttribute: ActionOnConstant {
    type Term;
    type Attribute;

    fn on_attribute_keyword(
        &mut self,
        range: Range,
        keyword: Keyword,
    ) -> ParsingResult<Self::Attribute>;
    fn on_attribute_constant(
        &mut self,
        range: Range,
        keyword: Keyword,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Attribute>;
    fn on_attribute_symbol(
        &mut self,
        range: Range,
        keyword: Keyword,
        symbol: Self::Str,
    ) -> ParsingResult<Self::Attribute>;
    fn on_attribute_named(
        &mut self,
        range: Range,
        name: Self::Str,
    ) -> ParsingResult<Self::Attribute>;
    fn on_attribute_pattern(
        &mut self,
        range: Range,
        patterns: Vec<Self::Term>,
    ) -> ParsingResult<Self::Attribute>;
}

pub trait ActionOnSort: ActionOnIdentifier {
    type Sort;

    fn on_sort(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        args: Vec<Self::Sort>,
    ) -> ParsingResult<Self::Sort>;
}

pub trait ActionOnTerm:
    ActionOnConstant + ActionOnIdentifier + ActionOnSort + ActionOnAttribute
{
    fn on_term_constant(
        &mut self,
        range: Range,
        constant: Self::Constant,
    ) -> ParsingResult<Self::Term>;
    /// sort is [Some] if the syntax is `(as identifier sort)`
    fn on_term_identifier(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term>;
    /// sort is [Some] if the syntax is `(as identifier sort)`
    fn on_term_app(
        &mut self,
        range: Range,
        identifier: Self::Identifier,
        sort: Option<Self::Sort>,
        args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term>;
    fn on_term_let(
        &mut self,
        range: Range,
        bindings: Vec<(Self::Str, Self::Term)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term>;
    fn on_term_lambda(
        &mut self,
        range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term>;
    fn on_term_exists(
        &mut self,
        range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term>;
    fn on_term_forall(
        &mut self,
        range: Range,
        names: Vec<(Self::Str, Self::Sort)>,
        body: Self::Term,
    ) -> ParsingResult<Self::Term>;
    /// cases is a vector of arms, each of which maps a pattern to a term called body.
    ///
    /// a pattern is a non-empty vector of symbols:
    /// 1. if there is only one symbol, then it is the name of the constructor.
    /// 2. if there are more symbols, then the 0th symbol is the name of the constructor, and the
    ///    rest are variables to capture corresponding fields.
    fn on_term_match(
        &mut self,
        range: Range,
        scrutinee: Self::Term,
        cases: Vec<(Pattern<Self::Str>, Self::Term)>,
    ) -> ParsingResult<Self::Term>;
    fn on_term_annotated(
        &mut self,
        range: Range,
        t: Self::Term,
        attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term>;
}

/// Implement this trait to specify parsing actions
///
/// Functions in this trait are called at proper time during parsing.
///
/// Specify the type members to specify the result of these functions
pub trait ParsingAction:
    ActionOnConstant + ActionOnIdentifier + ActionOnSort + ActionOnAttribute + ActionOnTerm
{
    /// Output type for a parsing tree of a command
    type Command;

    fn on_command_assert(&mut self, range: Range, t: Self::Term) -> ParsingResult<Self::Command>;
    fn on_command_check_sat(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_check_sat_assuming(
        &mut self,
        range: Range,
        terms: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_const(
        &mut self,
        range: Range,
        name: Self::Str,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_datatype(
        &mut self,
        range: Range,
        name: Self::Str,
        datatype: DatatypeDec<Self::Str, Self::Sort>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_datatypes(
        &mut self,
        range: Range,
        defs: Vec<DatatypeDef<Self::Str, Self::Sort>>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_fun(
        &mut self,
        range: Range,
        name: Self::Str,
        input_sorts: Vec<Self::Sort>,
        out_sort: Self::Sort,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_sort(
        &mut self,
        range: Range,
        name: Self::Str,
        arity: UBig,
    ) -> ParsingResult<Self::Command>;
    fn on_command_declare_sort_parameter(
        &mut self,
        range: Range,
        name: Self::Str,
    ) -> ParsingResult<Self::Command>;
    fn on_command_define_const(
        &mut self,
        range: Range,
        name: Self::Str,
        sort: Self::Sort,
        term: Self::Term,
    ) -> ParsingResult<Self::Command>;
    fn on_command_define_fun(
        &mut self,
        range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_define_fun_rec(
        &mut self,
        range: Range,
        definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_define_funs_rec(
        &mut self,
        range: Range,
        definitions: Vec<FunctionDef<Self::Str, Self::Sort, Self::Term>>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_define_sort(
        &mut self,
        range: Range,
        name: Self::Str,
        params: Vec<Self::Str>,
        sort: Self::Sort,
    ) -> ParsingResult<Self::Command>;
    fn on_command_echo(&mut self, range: Range, s: Self::Str) -> ParsingResult<Self::Command>;
    fn on_command_exit(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_assertions(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_assignment(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_info(&mut self, range: Range, kw: Keyword) -> ParsingResult<Self::Command>;
    fn on_command_get_model(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_option(&mut self, range: Range, kw: Keyword) -> ParsingResult<Self::Command>;
    fn on_command_get_proof(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_unsat_assumptions(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_unsat_core(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_get_value(
        &mut self,
        range: Range,
        ts: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command>;
    fn on_command_pop(&mut self, range: Range, lvl: UBig) -> ParsingResult<Self::Command>;
    fn on_command_push(&mut self, range: Range, lvl: UBig) -> ParsingResult<Self::Command>;
    fn on_command_reset(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_reset_assertions(&mut self, range: Range) -> ParsingResult<Self::Command>;
    fn on_command_set_info(
        &mut self,
        range: Range,
        attributes: Self::Attribute,
    ) -> ParsingResult<Self::Command>;
    fn on_command_set_logic(
        &mut self,
        range: Range,
        logic: Self::Str,
    ) -> ParsingResult<Self::Command>;
    fn on_command_set_option(
        &mut self,
        range: Range,
        attribute: Self::Attribute,
    ) -> ParsingResult<Self::Command>;
}

/// Use this object when only the grammatical validity of a SMTLib script matters
pub struct UnitAction;

impl ActionOnString for UnitAction {
    type Str = ();

    fn on_string(&mut self, _range: Range, _s: String) -> ParsingResult<Self::Str> {
        Ok(())
    }
}

impl ActionOnConstant for UnitAction {
    type Constant = ();

    fn on_constant_binary(
        &mut self,
        _range: Range,
        _bytes: Vec<u8>,
        _len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(())
    }

    fn on_constant_hexadecimal(
        &mut self,
        _range: Range,
        _bytes: Vec<u8>,
        _len: usize,
    ) -> ParsingResult<Self::Constant> {
        Ok(())
    }

    fn on_constant_decimal(
        &mut self,
        _range: Range,
        _decimal: DBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(())
    }

    fn on_constant_numeral(
        &mut self,
        _range: Range,
        _numeral: UBig,
    ) -> ParsingResult<Self::Constant> {
        Ok(())
    }

    fn on_constant_string(
        &mut self,
        _range: Range,
        _string: Self::Str,
    ) -> ParsingResult<Self::Constant> {
        Ok(())
    }

    fn on_constant_bool(&mut self, _range: Range, _boolean: bool) -> ParsingResult<Self::Constant> {
        Ok(())
    }
}

impl ActionOnIndex for UnitAction {
    type Index = ();

    fn on_index_numeral(&mut self, _range: Range, _index: UBig) -> ParsingResult<Self::Index> {
        Ok(())
    }

    fn on_index_symbol(&mut self, _range: Range, _index: Self::Str) -> ParsingResult<Self::Index> {
        Ok(())
    }

    fn on_index_hexadecimal(
        &mut self,
        _range: Range,
        _bytes: Vec<u8>,
        _len: usize,
    ) -> ParsingResult<Self::Index> {
        Ok(())
    }
}

impl ActionOnIdentifier for UnitAction {
    type Identifier = ();

    fn on_identifier(
        &mut self,
        _range: Range,
        _symbol: Self::Str,
        _indices: Vec<Self::Index>,
    ) -> ParsingResult<Self::Identifier> {
        Ok(())
    }
}

impl ActionOnAttribute for UnitAction {
    type Term = ();
    type Attribute = ();

    fn on_attribute_keyword(
        &mut self,
        _range: Range,
        _keyword: Keyword,
    ) -> ParsingResult<Self::Attribute> {
        Ok(())
    }

    fn on_attribute_constant(
        &mut self,
        _range: Range,
        _keyword: Keyword,
        _constant: Self::Constant,
    ) -> ParsingResult<Self::Attribute> {
        Ok(())
    }

    fn on_attribute_symbol(
        &mut self,
        _range: Range,
        _keyword: Keyword,
        _symbol: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(())
    }

    fn on_attribute_named(
        &mut self,
        _range: Range,
        _name: Self::Str,
    ) -> ParsingResult<Self::Attribute> {
        Ok(())
    }

    fn on_attribute_pattern(
        &mut self,
        _range: Range,
        _patterns: Vec<Self::Term>,
    ) -> ParsingResult<Self::Attribute> {
        Ok(())
    }
}

impl ActionOnSort for UnitAction {
    type Sort = ();

    fn on_sort(
        &mut self,
        _range: Range,
        _identifier: Self::Identifier,
        _args: Vec<Self::Sort>,
    ) -> ParsingResult<Self::Sort> {
        Ok(())
    }
}

impl ActionOnTerm for UnitAction {
    fn on_term_constant(
        &mut self,
        _range: Range,
        _constant: Self::Constant,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_identifier(
        &mut self,
        _range: Range,
        _identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_app(
        &mut self,
        _range: Range,
        _identifier: Self::Identifier,
        _sort: Option<Self::Sort>,
        _args: Vec<Self::Term>,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_let(
        &mut self,
        _range: Range,
        _bindings: Vec<(Self::Str, Self::Term)>,
        _body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_lambda(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        _body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_exists(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        _body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_forall(
        &mut self,
        _range: Range,
        _names: Vec<(Self::Str, Self::Sort)>,
        _body: Self::Term,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_match(
        &mut self,
        _range: Range,
        _scrutinee: Self::Term,
        _cases: Vec<(Pattern<Self::Str>, Self::Term)>,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }

    fn on_term_annotated(
        &mut self,
        _range: Range,
        _t: Self::Term,
        _attributes: Vec<Self::Attribute>,
    ) -> ParsingResult<Self::Term> {
        Ok(())
    }
}

impl ParsingAction for UnitAction {
    type Command = ();

    fn on_command_assert(&mut self, _range: Range, _t: Self::Term) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_check_sat(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_check_sat_assuming(
        &mut self,
        _range: Range,
        _terms: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_const(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_datatype(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _datatype: DatatypeDec<Self::Str, Self::Sort>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_datatypes(
        &mut self,
        _range: Range,
        _defs: Vec<DatatypeDef<Self::Str, Self::Sort>>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_fun(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _input_sorts: Vec<Self::Sort>,
        _out_sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_sort(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _arity: UBig,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_declare_sort_parameter(
        &mut self,
        _range: Range,
        _name: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_const(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _sort: Self::Sort,
        _term: Self::Term,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_fun(
        &mut self,
        _range: Range,
        _definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_fun_rec(
        &mut self,
        _range: Range,
        _definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_funs_rec(
        &mut self,
        _range: Range,
        _definitions: Vec<FunctionDef<Self::Str, Self::Sort, Self::Term>>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_define_sort(
        &mut self,
        _range: Range,
        _name: Self::Str,
        _params: Vec<Self::Str>,
        _sort: Self::Sort,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_echo(&mut self, _range: Range, _s: Self::Str) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_exit(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_assignment(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_info(&mut self, _range: Range, _kw: Keyword) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_model(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_option(
        &mut self,
        _range: Range,
        _kw: Keyword,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_proof(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_unsat_assumptions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_unsat_core(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_get_value(
        &mut self,
        _range: Range,
        _ts: Vec<Self::Term>,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_pop(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_push(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_reset(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_reset_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_info(
        &mut self,
        _range: Range,
        _attributes: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_logic(
        &mut self,
        _range: Range,
        _logic: Self::Str,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }

    fn on_command_set_option(
        &mut self,
        _range: Range,
        _attribute: Self::Attribute,
    ) -> ParsingResult<Self::Command> {
        Ok(())
    }
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::Tokenizer;
    use crate::smtlib2::ScriptParser;
    use derive_new::new;
    use std::fs;
    use std::path::PathBuf;

    #[derive(Debug, Default, new, PartialEq, Eq)]
    struct TestCommandFolder {
        assert_count: u32,
        check_sat_count: u32,
        check_sat_assuming_count: u32,
    }

    impl ActionOnString for TestCommandFolder {
        type Str = ();

        fn on_string(&mut self, _range: Range, _s: String) -> ParsingResult<Self::Str> {
            Ok(())
        }
    }

    impl ActionOnConstant for TestCommandFolder {
        type Constant = ();

        fn on_constant_binary(
            &mut self,
            _range: Range,
            _bytes: Vec<u8>,
            _len: usize,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }

        fn on_constant_hexadecimal(
            &mut self,
            _range: Range,
            _bytes: Vec<u8>,
            _len: usize,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }

        fn on_constant_decimal(
            &mut self,
            _range: Range,
            _decimal: DBig,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }

        fn on_constant_numeral(
            &mut self,
            _range: Range,
            _numeral: UBig,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }

        fn on_constant_string(
            &mut self,
            _range: Range,
            _string: Self::Str,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }

        fn on_constant_bool(
            &mut self,
            _range: Range,
            _boolean: bool,
        ) -> ParsingResult<Self::Constant> {
            Ok(())
        }
    }

    impl ActionOnIndex for TestCommandFolder {
        type Index = ();

        fn on_index_numeral(&mut self, _range: Range, _index: UBig) -> ParsingResult<Self::Index> {
            Ok(())
        }

        fn on_index_symbol(
            &mut self,
            _range: Range,
            _index: Self::Str,
        ) -> ParsingResult<Self::Index> {
            Ok(())
        }

        fn on_index_hexadecimal(
            &mut self,
            _range: Range,
            _bytes: Vec<u8>,
            _len: usize,
        ) -> ParsingResult<Self::Index> {
            Ok(())
        }
    }

    impl ActionOnIdentifier for TestCommandFolder {
        type Identifier = ();

        fn on_identifier(
            &mut self,
            _range: Range,
            _symbol: Self::Str,
            _indices: Vec<Self::Index>,
        ) -> ParsingResult<Self::Identifier> {
            Ok(())
        }
    }

    impl ActionOnAttribute for TestCommandFolder {
        type Term = ();
        type Attribute = ();

        fn on_attribute_keyword(
            &mut self,
            _range: Range,
            _keyword: Keyword,
        ) -> ParsingResult<Self::Attribute> {
            Ok(())
        }

        fn on_attribute_constant(
            &mut self,
            _range: Range,
            _keyword: Keyword,
            _constant: Self::Constant,
        ) -> ParsingResult<Self::Attribute> {
            Ok(())
        }

        fn on_attribute_symbol(
            &mut self,
            _range: Range,
            _keyword: Keyword,
            _symbol: Self::Str,
        ) -> ParsingResult<Self::Attribute> {
            Ok(())
        }

        fn on_attribute_named(
            &mut self,
            _range: Range,
            _name: Self::Str,
        ) -> ParsingResult<Self::Attribute> {
            Ok(())
        }

        fn on_attribute_pattern(
            &mut self,
            _range: Range,
            _patterns: Vec<Self::Term>,
        ) -> ParsingResult<Self::Attribute> {
            Ok(())
        }
    }

    impl ActionOnSort for TestCommandFolder {
        type Sort = ();

        fn on_sort(
            &mut self,
            _range: Range,
            _identifier: Self::Identifier,
            _args: Vec<Self::Sort>,
        ) -> ParsingResult<Self::Sort> {
            Ok(())
        }
    }

    impl ActionOnTerm for TestCommandFolder {
        fn on_term_constant(
            &mut self,
            _range: Range,
            _constant: Self::Constant,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_identifier(
            &mut self,
            _range: Range,
            _identifier: Self::Identifier,
            _sort: Option<Self::Sort>,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_app(
            &mut self,
            _range: Range,
            _identifier: Self::Identifier,
            _sort: Option<Self::Sort>,
            _args: Vec<Self::Term>,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_let(
            &mut self,
            _range: Range,
            _bindings: Vec<(Self::Str, Self::Term)>,
            _body: Self::Term,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_lambda(
            &mut self,
            _range: Range,
            _names: Vec<(Self::Str, Self::Sort)>,
            _body: Self::Term,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_exists(
            &mut self,
            _range: Range,
            _names: Vec<(Self::Str, Self::Sort)>,
            _body: Self::Term,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_forall(
            &mut self,
            _range: Range,
            _names: Vec<(Self::Str, Self::Sort)>,
            _body: Self::Term,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_match(
            &mut self,
            _range: Range,
            _scrutinee: Self::Term,
            _cases: Vec<(Pattern<Self::Str>, Self::Term)>,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }

        fn on_term_annotated(
            &mut self,
            _range: Range,
            _t: Self::Term,
            _attributes: Vec<Self::Attribute>,
        ) -> ParsingResult<Self::Term> {
            Ok(())
        }
    }

    impl ParsingAction for TestCommandFolder {
        type Command = ();

        fn on_command_assert(
            &mut self,
            _range: Range,
            _t: Self::Term,
        ) -> ParsingResult<Self::Command> {
            self.assert_count += 1;
            Ok(())
        }

        fn on_command_check_sat(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            self.check_sat_count += 1;
            Ok(())
        }

        fn on_command_check_sat_assuming(
            &mut self,
            _range: Range,
            _terms: Vec<Self::Term>,
        ) -> ParsingResult<Self::Command> {
            self.check_sat_assuming_count += 1;
            Ok(())
        }

        fn on_command_declare_const(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _sort: Self::Sort,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_declare_datatype(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _datatype: DatatypeDec<Self::Str, Self::Sort>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_declare_datatypes(
            &mut self,
            _range: Range,
            _defs: Vec<DatatypeDef<Self::Str, Self::Sort>>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_declare_fun(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _input_sorts: Vec<Self::Sort>,
            _out_sort: Self::Sort,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_declare_sort(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _arity: UBig,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_declare_sort_parameter(
            &mut self,
            _range: Range,
            _name: Self::Str,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_define_const(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _sort: Self::Sort,
            _term: Self::Term,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_define_fun(
            &mut self,
            _range: Range,
            _definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_define_fun_rec(
            &mut self,
            _range: Range,
            _definition: FunctionDef<Self::Str, Self::Sort, Self::Term>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_define_funs_rec(
            &mut self,
            _range: Range,
            _definitions: Vec<FunctionDef<Self::Str, Self::Sort, Self::Term>>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_define_sort(
            &mut self,
            _range: Range,
            _name: Self::Str,
            _params: Vec<Self::Str>,
            _sort: Self::Sort,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_echo(
            &mut self,
            _range: Range,
            _s: Self::Str,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_exit(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_assignment(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_info(
            &mut self,
            _range: Range,
            _kw: Keyword,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_model(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_option(
            &mut self,
            _range: Range,
            _kw: Keyword,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_proof(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_unsat_assumptions(
            &mut self,
            _range: Range,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_unsat_core(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_get_value(
            &mut self,
            _range: Range,
            _ts: Vec<Self::Term>,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_pop(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_push(&mut self, _range: Range, _lvl: UBig) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_reset(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_reset_assertions(&mut self, _range: Range) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_set_info(
            &mut self,
            _range: Range,
            _attributes: Self::Attribute,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_set_logic(
            &mut self,
            _range: Range,
            _logic: Self::Str,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }

        fn on_command_set_option(
            &mut self,
            _range: Range,
            _attribute: Self::Attribute,
        ) -> ParsingResult<Self::Command> {
            Ok(())
        }
    }

    fn get_test_input(filename: &str) -> String {
        let mut path = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        path.push("tests/resources");
        path.push(filename);
        fs::read_to_string(path).expect("Failed to read test input file: {filename}")
    }

    // Verify a command folder is called for every type of command.
    #[test]
    fn test_command_folder() {
        let filename = "all_commands.smt2";
        let script = get_test_input(filename);
        let mut folder = TestCommandFolder::default();
        ScriptParser::new()
            .parse(&mut folder, Tokenizer::new(script.chars(), false))
            .unwrap_or_else(|_| panic!("Failed to parse input file: {filename}"));
        assert_eq!(folder, TestCommandFolder::new(1, 1, 1));
    }
}
