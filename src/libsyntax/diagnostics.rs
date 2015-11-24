// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Diagnostic reporting.
//!
//! This module contains types and functions used to generate, format, and report **diagnostics**:
//! error and warning messages, notifications, etc.

/// Span of a token
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Span {
    /// Byte offset of the first character of the span
    pub from: usize,

    /// Byte offset of the first character following the span (after the last character)
    pub to: usize,
}

impl Span {
    /// Make a new span with given bounds
    pub fn new(from: usize, to: usize) -> Span {
        assert!(from <= to);
        Span { from: from, to: to }
    }
}

/// Reporter interface
///
/// Reporters are used to... report various errors, warnings, suggestions, threats, etc.
/// which are encountered while processing the source code. SpanReporter reports such things
/// in relation to some span of the source.
pub trait SpanReporter<'a> {
    /// Report an error
    fn error(&self, span: Span, message: &'a str);

    /// Report a warning
    fn warning(&self, span: Span, message: &'a str);
}
