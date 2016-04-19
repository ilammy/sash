// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Stub interface implementations.

use std::rc::Rc;
use std::cell::RefCell;

use syntax::diagnostics::{Reporter, Span, Severity};

/// A simple Reporter collecting diagnostics.
pub struct SinkReporter {
    /// Reporte diagnostics are collected into this vector.
    pub diagnostics: Rc<RefCell<Vec<(Severity, Span)>>>,
}

impl Reporter for SinkReporter {
    fn report(&mut self, severity: Severity, _: &str, loc: Option<Span>) {
        let mut diagnostics = self.diagnostics.borrow_mut();

        // Scanner diagnostics always come with a location.
        diagnostics.push((severity, loc.unwrap()));
    }
}

impl SinkReporter {
    /// Make a new reporter that will push all diagnostics into the given vector.
    pub fn new(diagnostics: Rc<RefCell<Vec<(Severity, Span)>>>) -> SinkReporter {
        SinkReporter {
            diagnostics: diagnostics,
        }
    }
}
