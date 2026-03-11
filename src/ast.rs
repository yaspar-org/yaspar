// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # AST data types
//!
//! This module contains the types that represent values parsed from SMT-LIB input:
//!
//! - [`GrammarError`] — errors produced during tokenization or grammar validation.
//! - [`Keyword`] — the set of predefined and user-defined SMT-LIB keywords.
//! - [`SortDec`], [`ConstructorDec`], [`DatatypeDec`], [`DatatypeDef`] — algebraic datatype
//!   declarations.
//! - [`FunctionDef`] — function definitions used by `define-fun`, `define-fun-rec`, and
//!   `define-funs-rec` commands.

use crate::position::Range;
use dashu::integer::UBig;
use phf::phf_map;
use serde::{Deserialize, Serialize};
use std::fmt::Display;

/// Errors that can occur during tokenization or grammar-level validation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum GrammarError {
    /// An invalid token was encountered at the given source range.
    TokenizeError { range: Range, buf: String },
    /// The number of sort declarations does not match the number of datatype definitions.
    DatatypeDeclarationError {
        range: Range,
        num_datatypes: usize,
        num_defs: usize,
    },
    /// The number of recursive function signatures does not match the number of bodies.
    RecFunsDefinitionError {
        range: Range,
        num_funs: usize,
        num_bodies: usize,
    },
    /// A catch-all for other grammar errors.
    Other { range: Range, message: String },
}

fn limit_str_len(s: &str, l: usize) -> String {
    if s.len() < l {
        s.to_string()
    } else {
        format!("{}...", &s[..l])
    }
}

impl Display for GrammarError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            GrammarError::TokenizeError { range, buf } => {
                write!(
                    f,
                    "invalid token '{}' from {} to {}!",
                    limit_str_len(buf, 15),
                    range.start,
                    range.end
                )
            }
            GrammarError::DatatypeDeclarationError {
                range,
                num_datatypes,
                num_defs,
            } => {
                write!(
                    f,
                    "datatype declaration {} declared {} datatypes but {} were given!",
                    range, num_datatypes, num_defs
                )
            }
            GrammarError::RecFunsDefinitionError {
                range,
                num_funs,
                num_bodies,
            } => {
                write!(
                    f,
                    "rec function definitions {} defined {} functions but {} bodies were given!",
                    range, num_funs, num_bodies
                )
            }
            GrammarError::Other { range, message } => {
                write!(f, "other error {}: {}", range, message)
            }
        }
    }
}

/// SMT-LIB keywords (`:keyword` syntax).
///
/// Predefined keywords for standard options and info flags are represented as dedicated
/// variants. All other keywords are captured by [`Keyword::Other`].
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum Keyword {
    // Options
    DiagnosticOutputChannel,
    GlobalDeclarations,
    InteractiveMode,
    PrintSuccess,
    ProduceAssertions,
    ProduceAssignments,
    ProduceModels,
    ProduceProofs,
    ProduceUnsatAssumptions,
    ProduceUnsatCores,
    RandomSeed,
    RegularOutputChannel,
    ReproducibleResourceLimit,
    Verbosity,

    // Info
    AllStatistics,
    AssertionStackLevel,
    Authors,
    ErrorBehavior,
    Name,
    ReasonUnknown,
    Version,

    Named,
    Pattern,
    /// this captures all other keywords
    Other(String),
}

pub static KEYWORD_MAP: phf::Map<&'static str, Keyword> = phf_map! {
    ":diagnostic-output-channel" => Keyword::DiagnosticOutputChannel,
    ":global-declarations" => Keyword::GlobalDeclarations,
    ":interactive-mode" => Keyword::InteractiveMode,
    ":print-success" => Keyword::PrintSuccess,
    ":produce-assertions" => Keyword::ProduceAssertions,
    ":produce-assignments" => Keyword::ProduceAssignments,
    ":produce-models" => Keyword::ProduceModels,
    ":produce-proofs" => Keyword::ProduceProofs,
    ":produce-unsat-assertions" => Keyword::ProduceUnsatAssumptions,
    ":produce-unsat-cores" => Keyword::ProduceUnsatCores,
    ":random-seed" => Keyword::RandomSeed,
    ":regular-output-channel" => Keyword::RegularOutputChannel,
    ":reproducible-resource-limit" => Keyword::ReproducibleResourceLimit,
    ":verbosity" => Keyword::Verbosity,
    ":all-statistics" => Keyword::AllStatistics,
    ":assertion-stack-level" => Keyword::AssertionStackLevel,
    ":authors" => Keyword::Authors,
    ":error-behavior" => Keyword::ErrorBehavior,
    ":name" => Keyword::Name,
    ":reason-unknown" => Keyword::ReasonUnknown,
    ":version" => Keyword::Version,
    ":named" => Keyword::Named,
    ":pattern" => Keyword::Pattern,
};

impl Keyword {
    /// Returns the keyword text without the leading colon.
    pub fn symbol_of(&self) -> &str {
        match self {
            Keyword::DiagnosticOutputChannel => "diagnostic-output-channel",
            Keyword::GlobalDeclarations => "global-declarations",
            Keyword::InteractiveMode => "interactive-mode",
            Keyword::PrintSuccess => "print-success",
            Keyword::ProduceAssertions => "produce-assertions",
            Keyword::ProduceAssignments => "produce-assignments",
            Keyword::ProduceModels => "produce-models",
            Keyword::ProduceProofs => "produce-proofs",
            Keyword::ProduceUnsatAssumptions => "produce-unsat-assertions",
            Keyword::ProduceUnsatCores => "produce-unsat-cores",
            Keyword::RandomSeed => "random-seed",
            Keyword::RegularOutputChannel => "regular-output-channel",
            Keyword::ReproducibleResourceLimit => "reproducible-resource-limit",
            Keyword::Verbosity => "verbosity",
            Keyword::AllStatistics => "all-statistics",
            Keyword::AssertionStackLevel => "assertion-stack-level",
            Keyword::Authors => "authors",
            Keyword::ErrorBehavior => "error-behavior",
            Keyword::Name => "name",
            Keyword::ReasonUnknown => "reason-unknown",
            Keyword::Version => "version",
            Keyword::Named => "named",
            Keyword::Pattern => "pattern",
            Keyword::Other(s) => s,
        }
    }
}

impl Display for Keyword {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, ":{}", self.symbol_of())
    }
}

/// A sort declaration: a name and its arity (number of sort parameters).
#[derive(Debug, Eq, PartialEq)]
pub struct SortDec<Str>(pub Str, pub UBig);

/// A constructor declaration within a datatype: a name and a list of (selector-name, sort) pairs.
#[derive(Debug, Eq, PartialEq)]
pub struct ConstructorDec<Str, S>(pub Str, pub Vec<(Str, S)>);

/// A function definition as used by `define-fun`, `define-fun-rec`, and `define-funs-rec`.
#[derive(Debug, Eq, PartialEq)]
pub struct FunctionDef<Str, S, T> {
    /// name of the function
    pub name: Str,
    /// variables of the function
    pub vars: Vec<(Str, S)>,
    /// the output sort of the function
    pub out_sort: S,
    /// the actual definition of the function
    pub body: T,
}

/// A datatype declaration, possibly parametric.
#[derive(Debug, Eq, PartialEq)]
pub struct DatatypeDec<Str, S> {
    /// sort parameters introduced by `par`
    ///
    /// an empty params means that the datatype is monomorphic.
    pub params: Vec<Str>,
    pub constructors: Vec<ConstructorDec<Str, S>>,
}

/// A named datatype definition, pairing a sort name with its [`DatatypeDec`].
#[derive(Debug, Eq, PartialEq)]
pub struct DatatypeDef<Str, S> {
    /// name of the datatype; sort
    pub name: Str,
    /// the actual definition
    pub dec: DatatypeDec<Str, S>,
}
