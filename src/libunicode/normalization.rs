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

use std::iter::{FromIterator, IntoIterator};
use tables::{decomposition_mappings, composition_mappings};

//
// Definitions of Normalization Forms
//

/// Normalize a string according to **Normalization Form D** (_D118_).
pub fn nfd(s: &str) -> String {
    let v = canonical_decomposition(s.chars());
    return String::from_iter(v.iter().map(|&(c, _)| c));
}

/// Normalize a string according to **Normalization Form KD** (_D119_).
pub fn nfkd(s: &str) -> String {
    let v = compatibility_decomposition(s.chars());
    return String::from_iter(v.iter().map(|&(c, _)| c));
}

/// Normalize a string according to **Normalization Form C** (_D120_).
pub fn nfc(s: &str) -> String {
    let mut v = canonical_decomposition(s.chars());
    compose_canonically(&mut v);
    return String::from_iter(v.iter().map(|&(c, _)| c));
}

/// Normalize a string according to **Normalization Form KC** (_D121_).
pub fn nfkc(s: &str) -> String {
    let mut v = compatibility_decomposition(s.chars());
    compose_canonically(&mut v);
    return String::from_iter(v.iter().map(|&(c, _)| c));
}

//
// Decomposition
//

/// Produce a Compatibility decomposition (D65) of a character sequence.
fn compatibility_decomposition<I>(chars: I) -> Vec<(char, u8)>
    where I: IntoIterator<Item=char>
{
    let mut buffer = Vec::new();

    for c in chars {
        push_compatibility_decomposition(c, &mut buffer);
    }

    reorder_canonically(&mut buffer[..]);

    return buffer;
}

/// Produce a Canonical decomposition (D68) of a character sequence.
fn canonical_decomposition<I>(chars: I) -> Vec<(char, u8)>
    where I: IntoIterator<Item=char>
{
    let mut buffer = Vec::new();

    for c in chars {
        push_canonical_decomposition(c, &mut buffer);
    }

    reorder_canonically(&mut buffer[..]);

    return buffer;
}

/// Push a Compatibility decomposition (D65) of a single character into the given buffer.
fn push_compatibility_decomposition(c: char, vec: &mut Vec<(char, u8)>) {
    use tables::properties::canonical_combining_class as ccc;

    if push_hangul_decomposition(c, vec) {
        return;
    }

    match decomposition_mappings::compatibility_mapping(c) {
        Some(decomposition) => {
            vec.extend_from_slice(decomposition);
        }
        None => {
            vec.push((c, ccc(c)));
        }
    }
}

/// Push a Canonical decomposition (D68) of a single character into the given buffer.
fn push_canonical_decomposition(c: char, vec: &mut Vec<(char, u8)>) {
    use tables::properties::canonical_combining_class as ccc;

    if push_hangul_decomposition(c, vec) {
        return;
    }

    match decomposition_mappings::canonical_mapping(c) {
        Some(decomposition) => {
            vec.extend_from_slice(decomposition);
        }
        None => {
            vec.push((c, ccc(c)));
        }
    }
}

//
// Conjoining Jamo Behavior
//

const S_BASE: u32 = 0xAC00;
const L_BASE: u32 = 0x1100;
const V_BASE: u32 = 0x1161;
const T_BASE: u32 = 0x11A7;
const L_COUNT: u32 = 19;
const V_COUNT: u32 = 21;
const T_COUNT: u32 = 28;
const N_COUNT: u32 = V_COUNT * T_COUNT;
const S_COUNT: u32 = L_COUNT * N_COUNT;

/// If a character is a Precomposed Hangul syllable (D132) then push its full decomposition into
/// the given buffer and return true. Otherwise do not modify the buffer and return false.
fn push_hangul_decomposition(c: char, vec: &mut Vec<(char, u8)>) -> bool {
    use std::char;
    use tables::properties::canonical_combining_class as ccc;

    if ((c as u32) < S_BASE) || ((S_BASE + S_COUNT) <= (c as u32)) {
        return false;
    }

    let s_index = (c as u32) - S_BASE;

    let l_index = s_index / N_COUNT;
    let v_index = (s_index % N_COUNT) / T_COUNT;
    let t_index = s_index % T_COUNT;

    // Computed Hangul syllables are guaranteed to be valid Unicode codepoints (cf. ranges).
    // They also have been assigned canonical combining class zero and canonical combining
    // class is guaranteed to not change in Unicode, so we can save a table lookup on that.

    if t_index > 0 {
        let l = char::from_u32(L_BASE + l_index).unwrap();
        let v = char::from_u32(V_BASE + v_index).unwrap();
        let t = char::from_u32(T_BASE + t_index).unwrap();

        assert!((ccc(l) == 0) && (ccc(v) == 0) && (ccc(t) == 0));

        vec.push((l, 0));
        vec.push((v, 0));
        vec.push((t, 0));
    } else {
        let l = char::from_u32(L_BASE + l_index).unwrap();
        let v = char::from_u32(V_BASE + v_index).unwrap();

        assert!((ccc(l) == 0) && (ccc(v) == 0));

        vec.push((l, 0));
        vec.push((v, 0));
    }

    return true;
}

/// If a character pair forms a Precomposed Hangul syllable (D132) when it is canonically composed
/// then return this Some composition. Otherwise return None.
fn compose_hangul(c1: char, c2: char) -> Option<(char, u8)> {
    use std::char;
    use tables::properties::canonical_combining_class as ccc;

    // In the same way as with decomposition, arithmetics and character ranges guarantee codepoint
    // validity here, and precomposed Hangul syllables also have canonical combining class zero.

    // <L, V> pair
    if ((L_BASE <= (c1 as u32)) && ((c1 as u32) < L_BASE + L_COUNT)) &&
       ((V_BASE <= (c2 as u32)) && ((c2 as u32) < V_BASE + V_COUNT))
    {
        let l_index = (c1 as u32) - L_BASE;
        let v_index = (c2 as u32) - V_BASE;

        let lv_index = l_index * N_COUNT + v_index * T_COUNT;

        let lv = char::from_u32(S_BASE + lv_index).unwrap();

        assert!(ccc(lv) == 0);

        return Some((lv, 0));
    }

    // <LV, T> pair
    if ((S_BASE <= (c1 as u32)) && ((c1 as u32) < S_BASE + S_COUNT)) &&
       (((c1 as u32) - S_BASE) % T_COUNT == 0) &&
       (((T_BASE + 1) <= (c2 as u32)) && ((c2 as u32) < T_BASE + T_COUNT))
    {
        let t_index = (c2 as u32) - T_BASE;

        let lvt = char::from_u32((c1 as u32) + t_index).unwrap();

        assert!(ccc(lvt) == 0);

        return Some((lvt, 0));
    }

    // Anything else
    return None;
}

//
// Canonical Ordering Algorithm
//

/// Check whether adjacent characters form a Reorderable pair (D108).
fn reorderable_pair(a: (char, u8), b: (char, u8)) -> bool {
    (a.1 > b.1) && (b.1 > 0)
}

/// Apply the Canonical Ordering Algorithm (D109) to a character slice.
fn reorder_canonically(slice: &mut [(char, u8)]) {
    // Bubble sort, yay!
    for lim in (1..slice.len()).rev() {
        for i in 0..lim {
            if reorderable_pair(slice[i], slice[i + 1]) {
                slice.swap(i, i + 1);
            }
        }
    }
}

//
// Canonical Composition Algorithm
//

/// Apply the Canonical Composition Algorithm (D117) to a character buffer.
fn compose_canonically(buffer: &mut Vec<(char, u8)>) {
    let mut ci = 1;
    while ci < buffer.len() {
        if let Some(li) = find_starter(&buffer[..], ci) {
            if !blocked(&buffer[..], li, ci) {
                if let Some(p) = primary_composite(buffer[li].0, buffer[ci].0) {
                    buffer[li] = p;
                    buffer.remove(ci);
                    continue;
                }
            }
        }
        ci += 1;
    }
}

/// Find the last Starter (D107) preceding C in a character slice.
/// This is step R1 of the Canonical Composition Algorithm (D117).
fn find_starter(slice: &[(char, u8)], ci: usize) -> Option<usize> {
    for li in (0..ci).rev() {
        if slice[li].1 == 0 {
            return Some(li);
        }
    }
    return None;
}

/// Verify that A is not blocked (D115) from C in a character slice.
/// This is the first part of step R2 of the Canonical Composition Algorithm (D117).
fn blocked(slice: &[(char, u8)], ai: usize, ci: usize) -> bool {
    assert!(ai < ci);

    let ccc_a = slice[ai].1;
    let ccc_c = slice[ci].1;

    if ccc_a == 0 {
        for bi in (ai + 1)..ci {
            let ccc_b = slice[bi].1;

            if (ccc_b == 0) || (ccc_b >= ccc_c) {
                return true;
            }
        }
    }

    return false;
}

/// Check for a Primary Composite (D114) equivalent to the given pair of characters.
/// This is the second part of step R2 of the Canonical Composition Algorithm (D117).
fn primary_composite(c1: char, c2: char) -> Option<(char, u8)> {
    compose_hangul(c1, c2).or_else(|| composition_mappings::primary(c1, c2))
}
