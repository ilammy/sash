// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash syntax analysis.
//!
//! This crate contains modules implementing the most front end of Sash front-end:
//!
//!   - lexical analysis
//!   - syntax analysis

extern crate unicode;

pub mod diagnostics;
pub mod expressions;
pub mod intern_pool;
pub mod lexer;
pub mod parser;
pub mod tokens;
