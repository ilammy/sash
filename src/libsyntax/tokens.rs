// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash token definitions.
//!
//! This module contains definitions of various tokens recognized and processed by Sash parser.

/// Types of tokens recognized by the scanner.
#[derive(Debug, PartialEq)]
pub enum Token {
    /// Marker token denoting the end-of-token-stream condition.
    EOF,

    /// Non-significant whitespace.
    Whitespace,

    /// Non-significant comment.
    Comment,

    /// Documentation comment.
    DocComment,

    /// Left (opening) parenthesis `(`.
    Lparen,

    /// Right (closing) parenthesis `)`.
    Rparen,

    /// Left (opening) bracket `[`.
    Lbrack,

    /// Right (closing) bracket `]`.
    Rbrack,

    /// Left (opening) brace `{`.
    Lbrace,

    /// Right (closing) brace `}`.
    Rbrace,

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

    /// An identifier (of any kind).
    Identifier,

    /// An implicit symbol.
    ImplicitSymbol,

    /// An explicit symbol.
    ExplicitSymbol,

    /// Marker token denoting invalid character sequences.
    Unrecognized,
}
