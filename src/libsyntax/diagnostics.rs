// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Diagnostic reporting.
//!
//! This module contains types and functions used to generate, format, and report **diagnostics**:
//! error and warning messages, notifications, etc.

use std::cell::RefCell;

/// Span of a token or an expression.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Span {
    /// Byte offset of the first character of the span.
    pub from: usize,

    /// Byte offset of the first character following the span (after the last character).
    pub to: usize,
}

impl Span {
    /// Makes a new span with given bounds.
    pub fn new(from: usize, to: usize) -> Span {
        assert!(from <= to);
        Span { from: from, to: to }
    }
}

/// Severity of a diagnostic.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Severity {
    /// The code is incorrect and the parser is unlikely to recover.
    Fatal,

    /// The code is incorrect.
    Error,
}

/// Reporter interface.
///
/// Reporters are used to... report various errors, warnings, suggestions, threats, (collectively
/// known as _diagnostics_) which are encountered while processing the source code.
pub trait Reporter {
    /// Report a diagnostic with given severity, message, and optional location.
    fn report(&mut self, severity: Severity, message: &str, loc: Option<Span>);
}

/// Convenience wrapper for easy reporting of diagnostics related to spans of source code.
pub struct Handler {
    reporter: RefCell<Box<Reporter>>,
}

impl Handler {
    /// Constructs a new Handler for a given reporter.
    pub fn with_reporter(reporter: Box<Reporter>) -> Handler {
        Handler {
            reporter: RefCell::new(reporter)
        }
    }

    /// Reports a fatal error at given span with the given message.
    pub fn fatal(&self, span: Span, message: &str) {
        self.reporter.borrow_mut().report(Severity::Fatal, message, Some(span));
    }

    /// Reports an error at given span with the given message.
    pub fn error(&self, span: Span, message: &str) {
        self.reporter.borrow_mut().report(Severity::Error, message, Some(span));
    }
}
