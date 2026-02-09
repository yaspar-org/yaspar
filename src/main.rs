// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! A simple cli to parse some smtlib and dump ouw what we parsed....

use clap::Parser;
use std::fs;
use std::time::Instant;
use yaspar::action::UnitAction;
use yaspar::smtlib2::ScriptParser;
use yaspar::tokenize_str;

#[derive(Parser, Debug)]
struct Cli {
    /// File containing smtlib formula
    file: String,
}

fn main() {
    let args = Cli::parse();
    let script = fs::read_to_string(&args.file).expect("Could not read test input file");
    let now = Instant::now();
    match ScriptParser::new().parse(&mut UnitAction, tokenize_str(&script, false)) {
        Ok(cmds) => {
            let runtime = now.elapsed().as_millis();
            println!("Parsed {} commands in {runtime} ms", cmds.len())
        }
        Err(e) => match e {
            lalrpop_util::ParseError::InvalidToken { location } => {
                println!("invalid token at {location}")
            }
            lalrpop_util::ParseError::UnrecognizedEof {
                location,
                expected: _,
            } => {
                println!("unexpected end-of-file at {location}")
            }
            lalrpop_util::ParseError::UnrecognizedToken { token, expected: _ } => {
                println!("unexpected token {} at {}", token.1, token.2)
            }
            lalrpop_util::ParseError::ExtraToken { token } => {
                println!("unexpected token {} at {}", token.1, token.2)
            }
            lalrpop_util::ParseError::User { error } => {
                println!("parser error: {}", error);
            }
        },
    }
}
