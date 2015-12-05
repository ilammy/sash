// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash token definitions.
//!
//! This module contains definitions of various tokens recognized and processed by Sash parser.

/// Types of tokens recognized by the scanner.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    /// Marker token denoting the end-of-token-stream condition.
    EOF,

    /// Non-significant whitespace.
    Whitespace,

    /// Non-significant comment.
    Comment,

    /// Documentation comment.
    DocComment,

    /// An opening (left) delimiter.
    OpenDelim(Delimiter),

    /// A closing (right) delimiter.
    CloseDelim(Delimiter),

    /// Dot `.`.
    Dot,

    /// Comma `,`.
    Comma,

    /// Colon `:`.
    Colon,

    /// Double colon `::`.
    Dualcolon,

    /// Semicolon `;`.
    Semicolon,

    /// Hash `#`.
    Hash,

    /// A literal value.
    Literal(Lit),

    /// An identifier (of any kind).
    Identifier,

    /// An implicit symbol.
    ImplicitSymbol,

    /// An explicit symbol.
    ExplicitSymbol,

    /// Marker token denoting invalid character sequences.
    Unrecognized,
}

/// Delimiter type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Delimiter {
    /// Parentheses `( )`.
    Paren,

    /// Brackets `[ ]`.
    Bracket,

    /// Braces `{ }`.
    Brace,
}

/// Literal token type.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Lit {
    /// An integer literal.
    Integer,

    /// A floating-point literal.
    Float,

    /// A single character.
    Character,

    /// A string of characters.
    String,

    /// A raw string of characters.
    RawString,
}
