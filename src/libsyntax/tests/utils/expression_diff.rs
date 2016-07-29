// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Test utilities: expression diff.
//!
//! This module contains utilities for comparing `Expression`s.

use syntax::expressions::{Expression, ExpressionKind};

/// Result of expression comparison.
#[derive(PartialEq, Eq)]
pub enum ComparisonResult {
    /// Expressions are fully identical.
    Identical,

    /// Types of the expressions match, but the contents don't.
    Matching,

    /// Types of the expressions do not match.
    Different,
}

/// Match two tree-structured enum references.
///
/// The delimiter syntax is kinda quirky, but that's Rust macros for you. Deal with it.
/// Copypasting matches is much more convoluted. The macro enforces full coverage of
/// enum variant pairs, so you can't miss them.
macro_rules! unify_match {
    (($actual_term:expr, $expected_term:expr) => {
        $(
            $variant:path {
                $($field:ident: ($actual_name:ident, $expected_name:ident)),*
            } => $then_body:block
        ),*
        ; else $else_body:block
    }) => {
        match $actual_term {
        $(
            &$variant { $($field: ref $actual_name,)* } => {
                match $expected_term {
                    &$variant { $($field: ref $expected_name,)* } => $then_body
                    _ => $else_body
                }
            }
        )*
        }
    };
}

/// Compare contents of two expressionss while ignoring their spans.
pub fn compare(actual: &Expression, expected: &Expression) -> ComparisonResult {
    unify_match!((&actual.kind, &expected.kind) => {
        ExpressionKind::ImplicitModule {
            body: (body_a, body_e)
        } => {
            compare_slices(body_a, body_e)
        },
        ExpressionKind::Library {
            name: (name_a, name_e),
            body: (body_a, body_e)
        } => {
            if name_a != name_e {
                ComparisonResult::Matching
            } else {
                compare_slices(body_a, body_e)
            }
        },
        ExpressionKind::Module {
            name: (name_a, name_e),
            body: (body_a, body_e)
        } => {
            if name_a != name_e {
                ComparisonResult::Matching
            } else {
                compare_slices(body_a, body_e)
            }
        },
        ExpressionKind::Unrecognized {} => { ComparisonResult::Identical };
        else {
            ComparisonResult::Different
        }
    })
}

/// Compare two expression sequences.
///
/// Note that this cannot return ComparisonResult::Different.
fn compare_slices(actual: &[Expression], expected: &[Expression]) -> ComparisonResult {
    if actual.len() != expected.len() {
        return ComparisonResult::Matching;
    }

    for (ref actual, ref expected) in actual.iter().zip(expected.iter()) {
        match compare(actual, expected) {
            ComparisonResult::Different | ComparisonResult::Matching => {
                return ComparisonResult::Matching;
            }
            ComparisonResult::Identical => { continue; }
        }
    }

    return ComparisonResult::Identical;
}
