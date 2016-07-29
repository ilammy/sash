// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash expression definitions.
//!
//! This module contains definitions of various expressions recognized and processed by Sash
//! parser.

use diagnostics::{Span};
use intern_pool::{Atom};

/// An expression recognized by the parser.
#[derive(PartialEq, Eq)]
pub struct Expression {
    /// The kind of the expression.
    pub kind: ExpressionKind,

    /// The span of the expression.
    pub span: Span,
}

/// Types of expressions recognized by the parser.
#[derive(PartialEq, Eq)]
pub enum ExpressionKind {
    /// A top-level implicit module.
    ImplicitModule {
        body: Vec<Expression>,
    },

    /// A top-level library definition.
    Library {
        name: Atom,
        body: Vec<Expression>,
    },

    /// A nested explicit module.
    Module {
        name: Atom,
        body: Vec<Expression>,
    },

    /// An unrecognized sequence of tokens.
    Unrecognized,
}
