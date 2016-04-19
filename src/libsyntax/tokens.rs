// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash token definitions.
//!
//! This module contains definitions of various tokens recognized and processed by Sash parser.

use intern_pool::Atom;

/// Types of tokens recognized by the scanner.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Token {
    /// Marker token denoting the end-of-token-stream condition.
    Eof,

    /// Non-significant whitespace.
    Whitespace,

    /// Non-significant comment.
    Comment,

    /// Documentation comment.
    DocComment(Atom),

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
    Literal(Lit, Option<Atom>),

    /// An identifier (of any kind).
    Identifier(Atom),

    /// An implicit symbol.
    ImplicitSymbol(Atom),

    /// An explicit symbol.
    ExplicitSymbol(Atom),

    /// A keyword.
    Keyword(Keyword),

    /// Marker token denoting invalid character sequences.
    Unrecognized,
}

/// Delimiter type.
#[derive(Debug, PartialEq, Eq, Clone, Copy)]
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
    Integer(Atom),

    /// A floating-point literal.
    Float(Atom),

    /// A single character.
    Character(Atom),

    /// A string of characters.
    String(Atom),

    /// A raw string of characters.
    RawString(Atom),
}

/// Literal keyword.
#[derive(Debug, PartialEq, Eq, Clone)]
pub enum Keyword {
    /// `library`.
    Library,

    /// `module`.
    Module,
}
