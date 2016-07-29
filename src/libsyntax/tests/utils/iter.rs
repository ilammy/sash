// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Iterator utilities.

use std::iter::Iterator;

/// Non-short-circuiting version of `Zip`. See `longest_zip()` for details.
pub struct LongestZip<A, B> {
    a: A,
    b: B,
}

impl<A, B> Iterator for LongestZip<A, B> where A: Iterator, B: Iterator {
    type Item = (Option<A::Item>, Option<B::Item>);

    fn next(&mut self) -> Option<Self::Item> {
        let v_a = self.a.next();
        let v_b = self.b.next();

        if v_a.is_some() || v_b.is_some() {
            return Some((v_a, v_b));
        } else {
            return None;
        }
    }
}

/// Returns an iterator which simulataneously walks over two other iterators until _both_ of
/// them are exhausted. It is similar to `zip()` method of `Iterator`, but it does not stop
/// when one of the iterators in exhausted.
///
/// Example:
/// ```
/// assert_eq!(longest_zip(&[1, 2, 3], &[5, 6]).collect::<Vec<_>>(),
///     &[
///         (Some(&1), Some(&5)),
///         (Some(&2), Some(&6)),
///         (Some(&3), None)
///     ]);
/// ```
pub fn longest_zip<A, B>(iter1: A, iter2: B) -> LongestZip<A::IntoIter, B::IntoIter>
    where A: IntoIterator, B: IntoIterator
{
    LongestZip { a: iter1.into_iter(), b: iter2.into_iter() }
}
