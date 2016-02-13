// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Unicode normalization algorithms.
//!
//! This module implements _Unicode Normalization Forms_ as defined by [Unicode Standard
//! Annex #15][UAX-15]. Unicode normalization is used to ensure that visually equivalent
//! strings have equivalent binary representations.
//!
//! [UAX-15]: http://www.unicode.org/reports/tr15/

//
// Definitions of Normalization Forms
//

/// Normalize a string according to **Normalization Form D** (_D118_).
pub fn nfd(s: &str) -> String {
    return s.to_owned();
}

/// Normalize a string according to **Normalization Form KD** (_D119_).
pub fn nfkd(s: &str) -> String {
    return s.to_owned();
}

/// Normalize a string according to **Normalization Form C** (_D120_).
pub fn nfc(s: &str) -> String {
    return s.to_owned();
}

/// Normalize a string according to **Normalization Form KC** (_D121_).
pub fn nfkc(s: &str) -> String {
    return s.to_owned();
}
