// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Parser test suite.
//!
//! This verifies all expressions parseable by Sash parser.

extern crate syntax;

use syntax::parser::{Parser};
use syntax::diagnostics::{Handler};
use syntax::expressions::{Expression};
use syntax::intern_pool::{InternPool};
use syntax::lexer::{StringScanner};

mod utils {
    pub mod expression_builders;
    pub mod expression_diff;
    pub mod stubs;
}

use utils::expression_builders::{ImplicitModule, Library, Module, Unrecognized};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Smoke test of test harness

#[test]
fn empty_stream() {
    verify_parser_output("", ImplicitModule::new());
}

#[test]
fn empty_stream_whitespace_and_comments() {
    verify_parser_output("
// test test test

/* another test */",
    ImplicitModule::new());
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Unrecognized expressions

#[test]
fn unrecognized_block_skip_simple() {
    verify_parser_output("
module first {}

wagon { foo bar }

module second {}
",
    ImplicitModule::new()
        .push(Module::new("first"))
        .push(Unrecognized::new())
        .push(Module::new("second")));
}

#[test]
fn unrecognized_block_skip_with_parens() {
    verify_parser_output("
module first {}

beaver (foo bar) { zog; }

module second {}
",
    ImplicitModule::new()
        .push(Module::new("first"))
        .push(Unrecognized::new())
        .push(Module::new("second")));
}

#[test]
fn unrecognized_block_cant_recover_unmatched() {
    verify_parser_failure("
module first {}

giraffe[X] { unbalanced :) }

module second {}");
}

#[test]
fn unrecognized_statement_skip_simple_1() {
    verify_parser_output("
module first {}

exterminate [all] \"humans\";

module second {}
",
    ImplicitModule::new()
        .push(Module::new("first"))
        .push(Unrecognized::new())
        .push(Module::new("second")));
}

#[test]
fn unrecognized_statement_skip_simple_2() {
    verify_parser_output("
module first {}

this = was(a, triumph);

module second {}
",
    ImplicitModule::new()
        .push(Module::new("first"))
        .push(Unrecognized::new())
        .push(Module::new("second")));
}

#[test]
fn unrecognized_statement_skip_after_block() {
    verify_parser_output("
module first {}

x{};

module second {}
",
    ImplicitModule::new()
        .push(Module::new("first"))
        .push(Unrecognized::new())
        .push(Unrecognized::new())
        .push(Module::new("second")));
}

#[test]
fn unrecognized_statement_cant_recover_unmatched_1() {
    verify_parser_failure("
module first {}

bork}

module second {}");
}

#[test]
fn unrecognized_statement_cant_recover_unmatched_2() {
    verify_parser_failure("
module first {}

bork]

module second {}");
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Modules

#[test]
fn modules_basic() {
    verify_parser_output("
// Simple module
module example1
{
}

// Nested modules
module example2
{
    module nested
    {
    }
}

// Unicode-named modules
module \u{043F}\u{0440}\u{0438}\u{043C}\u{0435}\u{0440}
{
}",
    ImplicitModule::new()
        .push(Module::new("example1"))
        .push(Module::new("example2")
            .push(Module::new("nested")))
        .push(Module::new("\u{043F}\u{0440}\u{0438}\u{043C}\u{0435}\u{0440}")));
}

#[test]
fn modules_recover_invalid_names() {
    verify_parser_output("
// Missing name
module {}

// Invalid name
module \"foo\" {}

// Seriously invalid name
module (2 + 2) * foo[bar] {}

// Nesting
module 1::2::3
{
    module A
    {
        module ### {}
        module B B
        {
            module '\u{4567}'{}
        }
        module .{}
    }
}",
    ImplicitModule::new()
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>")
            .push(Module::new("A")
                .push(Module::new("<invalid-name>"))
                .push(Module::new("<invalid-name>")
                    .push(Module::new("<invalid-name>")))
                .push(Module::new("<invalid-name>")))));
}

#[test]
fn modules_recover_non_block() {
    verify_parser_output("
// Missing name
module;

// Invalid name
module \"foo\";

// Seriously invalid name
module !@#$%^&*

// Nesting
module foo
{
    module bar;

    module baz + zog
    {
        module module module
    }
}",
    ImplicitModule::new()
        .push(Unrecognized::new())
        .push(Unrecognized::new())
        .push(Unrecognized::new())
        .push(Module::new("foo")
            .push(Unrecognized::new())
            .push(Module::new("<invalid-name>")
                .push(Unrecognized::new())
                .push(Unrecognized::new())
                .push(Unrecognized::new()))));
}

#[test]
fn modules_recover_delimited_expressions() {
    verify_parser_output("
// Parentheses
module () {}
module (something) {}
module (something(other), else) {}

// Brackets
module[] {}
module[u32] {}
module[Foo[bar]] {}

// Mixed
module[(;)(:)[(\\/)_..!._(\\/)][]]
{
    module(module(module{}))
    {
        module
        [
            module
        ]
    }
}
",
    ImplicitModule::new()
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>"))
        .push(Module::new("<invalid-name>")
            .push(Module::new("<invalid-name>")
                .push(Unrecognized::new()))));
}

#[test]
fn modules_cant_recover_eof_keyword() {
    verify_parser_failure("
module
");
}

#[test]
fn modules_cant_recover_eof_name() {
    verify_parser_failure("
module foo
");
}

#[test]
fn modules_cant_recover_eof_name_2() {
    verify_parser_failure("
module foo bar baz
");
}

#[test]
fn modules_cant_recover_eof_missing_brace() {
    verify_parser_failure("
module A {
");
}

#[test]
fn modules_cant_recover_eof_missing_brace_2() {
    verify_parser_failure("
module {
    module
");
}

#[test]
fn modules_cant_recover_unmatched_delimiter_1() {
    verify_parser_failure("
module :)
");
}

#[test]
fn modules_cant_recover_unmatched_delimiter_2() {
    verify_parser_failure("
module [test[)]
");
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Libraries

#[test]
fn libraries_basic() {
    verify_parser_output("
// Simple library
library example1
{
}

// Nested modules
library example2
{
    library nested
    {
    }
}

// Unicode-named modules
library \u{043F}\u{0440}\u{0438}\u{043C}\u{0435}\u{0440}
{
}",
    ImplicitModule::new()
        .push(Library::new("example1"))
        .push(Library::new("example2")
            .push(Library::new("nested")))
        .push(Library::new("\u{043F}\u{0440}\u{0438}\u{043C}\u{0435}\u{0440}")));
}

#[test]
fn libraries_recover_invalid_names() {
    verify_parser_output("
// Missing name
library {}

// Invalid name
library \"foo\" {}

// Seriously invalid name
library (2 + 2) * foo[bar] {}

// Nesting
library 1::2::3
{
    library A
    {
        library ### {}
        library B B
        {
            library '\u{4567}'{}
        }
        library .{}
    }
}",
    ImplicitModule::new()
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>")
            .push(Library::new("A")
                .push(Library::new("<invalid-name>"))
                .push(Library::new("<invalid-name>")
                    .push(Library::new("<invalid-name>")))
                .push(Library::new("<invalid-name>")))));
}

#[test]
fn libraries_recover_non_block() {
    verify_parser_output("
// Missing name
library;

// Invalid name
library \"foo\";

// Seriously invalid name
library !@#$%^&*

// Nesting
library foo
{
    library bar;

    library baz + zog
    {
        library library library
    }
}",
    ImplicitModule::new()
        .push(Unrecognized::new())
        .push(Unrecognized::new())
        .push(Unrecognized::new())
        .push(Library::new("foo")
            .push(Unrecognized::new())
            .push(Library::new("<invalid-name>")
                .push(Unrecognized::new())
                .push(Unrecognized::new())
                .push(Unrecognized::new()))));
}

#[test]
fn libraries_recover_delimited_expressions() {
    verify_parser_output("
// Parentheses
library () {}
library (something) {}
library (something(other), else) {}

// Brackets
library[] {}
library[u32] {}
library[Foo[bar]] {}

// Mixed
library[(;)(:)[(\\/)_..!._(\\/)][]]
{
    library(library(library{}))
    {
        library
        [
            library
        ]
    }
}
",
    ImplicitModule::new()
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>"))
        .push(Library::new("<invalid-name>")
            .push(Library::new("<invalid-name>")
                .push(Unrecognized::new()))));
}

#[test]
fn libraries_cant_recover_eof_keyword() {
    verify_parser_failure("
library
");
}

#[test]
fn libraries_cant_recover_eof_name() {
    verify_parser_failure("
library foo
");
}

#[test]
fn libraries_cant_recover_eof_name_2() {
    verify_parser_failure("
library foo bar baz
");
}

#[test]
fn libraries_cant_recover_eof_missing_brace() {
    verify_parser_failure("
library A {
");
}

#[test]
fn libraries_cant_recover_eof_missing_brace_2() {
    verify_parser_failure("
library {
    library
");
}

#[test]
fn libraries_cant_recover_unmatched_delimiter_1() {
    verify_parser_failure("
library :)
");
}

#[test]
fn libraries_cant_recover_unmatched_delimiter_2() {
    verify_parser_failure("
library [test[)]
");
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Test helpers

use std::rc::Rc;
use std::cell::RefCell;

use utils::expression_builders::{Build};
use utils::expression_diff::{self, ComparisonResult};
use utils::stubs::{SinkReporter};

/// Verify that the parser yields expected expressions when faced with the token stream produced
/// from the given string. Panic if this is not so.
fn verify_parser_output<B: Build>(input: &str, expected: B) {
    let pool = InternPool::new();

    let actual = process_test_string(input, &pool);

    match actual.len() {
        0 => panic!("parser did not produce output"),
        1 => { /* okay */ },
        _ => panic!("parser is not exhausted after parsing the whole token stream"),
    }

    let expected = expected.build_with(&pool);

    assert!(verify_expression(actual.first().unwrap(), &expected, &pool));
}

/// Verify that the parser fails to recover from errors present in the given string and does not
/// produce any output. Panics if the parser outputs something.
fn verify_parser_failure(input: &str) {
    let pool = InternPool::new();

    let actual = process_test_string(input, &pool);

    assert!(actual.is_empty());
}

/// Tokenize and parse the given strings. Return the expressions produced by the parser.
fn process_test_string(string: &str, pool: &InternPool) -> Vec<Expression> {
    let scanner_diagnostics = Rc::new(RefCell::new(Vec::new()));
    let scanner_reporter = SinkReporter::new(scanner_diagnostics.clone());
    let scanner_handler = Handler::with_reporter(Box::new(scanner_reporter));

    let tokens = StringScanner::new(string, &pool, &scanner_handler);

    let parser_diagnostics = Rc::new(RefCell::new(Vec::new()));
    let parser_reporter = SinkReporter::new(parser_diagnostics.clone());
    let parser_handler = Handler::with_reporter(Box::new(parser_reporter));

    let mut parser = Parser::new(tokens, &pool, &parser_handler);

    let mut exprs = Vec::new();

    while let Some(expr) = parser.parse_all() {
        exprs.push(expr);
    }

    return exprs;
}

/// Compare actual parsing results to expected. Return true if they match.
fn verify_expression(actual: &Expression, expected: &Expression, _: &InternPool) -> bool {
    expression_diff::compare(actual, expected) == ComparisonResult::Identical
}
