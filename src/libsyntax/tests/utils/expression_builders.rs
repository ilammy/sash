// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Test utilities: expression builders.
//!
//! This module contains utilities for building `Expression`s.

use syntax::diagnostics::{Span};
use syntax::expressions::{Expression, ExpressionKind};
use syntax::intern_pool::{InternPool};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Build trait
//

/// Lazily buildable expression.
///
/// This is used to build `Expression` instances which user proper `Atom`s for named things
/// while using just strings in test code.
pub trait Build {
    /// Render this buildable expression.
    fn build_with(&self, pool: &InternPool) -> Expression;
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Helper functions
//

/// Build an expression with dummy span.
fn build_expression(kind: ExpressionKind) -> Expression {
    Expression {
        kind: kind,
        span: Span::new(0, 0),
    }
}

/// Build a vec of an expressions.
fn build_vec(vec: &Vec<Box<Build>>, pool: &InternPool) -> Vec<Expression> {
    vec.iter().map(|ref e| e.build_with(pool)).collect()
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Buildable expressions
//

/// A delayed ExpressionKind::Unrecognized.
pub struct Unrecognized;

impl Unrecognized {
    /// Make a new Unrecognized.
    pub fn new() -> Unrecognized {
        Unrecognized
    }
}

impl Build for Unrecognized {
    fn build_with(&self, _: &InternPool) -> Expression {
        build_expression(
            ExpressionKind::Unrecognized)
    }
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

/// A delayed ExpressionKind::ImplicitModule.
pub struct ImplicitModule {
    body: Vec<Box<Build>>,
}

impl ImplicitModule {
    /// Make a new ImplicitModule with an empty body.
    pub fn new() -> ImplicitModule {
        ImplicitModule {
            body: Vec::new(),
        }
    }

    /// Add a buildable expression to this module's body.
    pub fn push<E: Build + 'static>(mut self, e: E) -> Self {
        self.body.push(Box::new(e));
        self
    }
}

impl Build for ImplicitModule {
    fn build_with(&self, pool: &InternPool) -> Expression {
        build_expression(
            ExpressionKind::ImplicitModule {
                body: build_vec(&self.body, pool),
        })
    }
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

/// A delayed ExpressionKind::Library.
pub struct Library {
    name: String,
    body: Vec<Box<Build>>,
}

impl Library {
    /// Make a new Library with an empty body and a given name.
    pub fn new(name: &str) -> Library {
        Library {
            name: name.to_owned(),
            body: Vec::new(),
        }
    }

    /// Add a buildable expression to this library's body.
    pub fn push<E: Build + 'static>(mut self, e: E) -> Self {
        self.body.push(Box::new(e));
        self
    }
}

impl Build for Library {
    fn build_with(&self, pool: &InternPool) -> Expression {
        build_expression(
            ExpressionKind::Library {
                name: pool.intern(&self.name),
                body: build_vec(&self.body, pool),
        })
    }
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -

/// A delayed ExpressionKind::Module.
pub struct Module {
    name: String,
    body: Vec<Box<Build>>,
}

impl Module {
    /// Make a new Module with an empty body and a given name.
    pub fn new(name: &str) -> Module {
        Module {
            name: name.to_owned(),
            body: Vec::new(),
        }
    }

    /// Add a buildable expression to this module's body.
    pub fn push<E: Build + 'static>(mut self, e: E) -> Self {
        self.body.push(Box::new(e));
        self
    }
}

impl Build for Module {
    fn build_with(&self, pool: &InternPool) -> Expression {
        build_expression(
            ExpressionKind::Module {
                name: pool.intern(&self.name),
                body: build_vec(&self.body, pool),
        })
    }
}
