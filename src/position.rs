// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

//! # Source position tracking
//!
//! Types for tracking source locations within an SMT-LIB input stream.
//! Every token and error carries a [`Range`] (start/end [`Position`]) so that
//! diagnostics can point to the exact location in the source text.

use std::fmt::Display;

/// A position in the source text, tracking line, column, and absolute character offset.
///
/// All fields are 0-based internally. The [`Display`] implementation shows 1-based
/// line and column numbers for human-readable output.
// todo: lalrpop requires position information to implement Copy. this is not optimal. remove Copy once lalrpop fixes this problem
#[derive(Debug, Copy, Clone, PartialEq, Eq, Hash)]
pub struct Position {
    /// Line number; 0 based
    pub lin_num: usize,
    /// Column number in a line; 0 based
    pub col_num: usize,
    /// character count; 0 based
    pub char_num: usize,
}

impl Display for Position {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "line {}, column {}", 1 + self.lin_num, 1 + self.col_num)
    }
}

impl Position {
    /// Creates a position at the origin (line 0, column 0, char 0).
    pub fn empty() -> Self {
        Self {
            lin_num: 0,
            col_num: 0,
            char_num: 0,
        }
    }

    /// Advances the position by one character. Newlines reset the column and increment the line.
    pub fn incr(&mut self, c: char) {
        self.char_num += 1;
        if c == '\n' {
            self.lin_num += 1;
            self.col_num = 0;
        } else {
            self.col_num += 1;
        }
    }
}

impl Default for Position {
    fn default() -> Self {
        Self::empty()
    }
}

/// A half-open source range `[start, end)` used to locate tokens and errors.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Range {
    pub start: Position,
    /// exclusive
    pub end: Position,
}

impl Range {
    pub fn new(start: Position, end: Position) -> Self {
        Self { start, end }
    }
}

impl Display for Range {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "from {} to {} (exclusive)", self.start, self.end)
    }
}
