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
///
/// The diagnostics may be reported either immediately using methods like
/// [`error()`](#method.error), or they can be constructed incrementally with the help of methods
/// like [`prepare_error()`](#method.prepare_error).
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

    /// Start building a fatal error at given span with the given message.
    pub fn prepare_fatal<'a>(&'a self, span: Span, message: &str) -> DiagnosticBuilder<'a> {
        let mut diagnostic = DiagnosticBuilder::new(&self.reporter, Severity::Fatal, message);
        diagnostic.span(span);
        return diagnostic;
    }

    /// Start building an error at given span with the given message.
    pub fn prepare_error<'a>(&'a self, span: Span, message: &str) -> DiagnosticBuilder<'a> {
        let mut diagnostic = DiagnosticBuilder::new(&self.reporter, Severity::Error, message);
        diagnostic.span(span);
        return diagnostic;
    }
}

/// Delayed diagnostic builder.
///
/// Some errors produce diagnostics which may be refined on upper processsing levels. This builder
/// allows to construct an initial diagnostic and keep this data around while the error bubbles up
/// to higher levels. Callers may fill in additional data before finally reporting the diagnostic.
///
/// Builders cannot be directly instantiated. Use [`Handler`'s](struct.Handler.html) methods like
/// [`prepare_fatal()`](struct.Handler.html#method.prepare_fatal) to start building a diagnostic.
/// The diagnostic can then be reported to the handler's `Reporter` with
/// [`report()`](#method.report).
///
/// The builder is marked with `#[must_use]` and will panic if [`report()`](#method.report)
/// has not been called during its lifetime. This ensures that diagnostics cannot be lost
/// during processing.
#[must_use]
pub struct DiagnosticBuilder<'a> {
    /// The reporter that will be used to report this diagnostic when it is complete.
    reporter: &'a RefCell<Box<Reporter>>,

    /// Set to true when the diagnostic has been reported.
    completed: bool,

    /// Diagnostic severity.
    severity: Severity,

    /// Diagnostic message.
    message: String,

    /// Diagnostic location (optional).
    location: Option<Span>,
}

impl<'a> DiagnosticBuilder<'a> {
    /// Make a new diagnostic builder.
    ///
    /// This is an internal convenience wrapper for builder construction. Use Handler's methods
    /// to instantiate properly filled-in diagnostic builders.
    fn new(reporter: &'a RefCell<Box<Reporter>>, severity: Severity, message: &str)
        -> DiagnosticBuilder<'a>
    {
        DiagnosticBuilder {
            reporter: reporter,
            completed: false,
            severity: severity,
            message: message.to_owned(),
            location: None,
        }
    }

    /// Report the complete diagnostic.
    ///
    /// Each diagnostic is reported only once.
    pub fn report(&mut self) {
        if self.completed {
            return;
        }
        self.reporter.borrow_mut().report(self.severity, &self.message, self.location);
        self.completed = true;
    }

    /// Set the span of the diagnostic.
    pub fn span(&mut self, span: Span) -> &mut Self {
        self.location = Some(span);
        self
    }
}

/// Panic if the constructed diagnostic has not been reported yet.
impl<'a> Drop for DiagnosticBuilder<'a> {
    fn drop(&mut self) {
        if !self.completed {
            panic!("dropped incomplete diagnostic")
        }
    }
}
