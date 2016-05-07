// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Diffing trees.
//!
//! Trees are more complex than sequences. Slices are enough to represent diffable sequences, but
//! for trees we need to know the internal structure of their nodes. One will need to provide an
//! implementation of the `TreeNode` trait which provides access to child nodes of a given node.
//!
//! Also, tree diff expects that provided comparators or `Eq` implementation compare only immediate
//! labels of the nodes, without doing a deep comparison of their child nodes. Failure to observe
//! this expectation results into over-conservative diffs (though, they are _not_ incorrect). Know
//! that derived implementations of `Eq` usually do a deep comparison, so you will usually need to
//! write an explicit comparator anyway.

use utils::diff::sequence;
use utils::tree::{TreeNode};

/// Result of tree node comparison.
#[derive(Debug, PartialEq)]
pub enum Diff<'a, T> where T: 'a {
    /// Node is present only in the left tree.
    Left(&'a T),

    /// Node is present only in the right tree.
    Right(&'a T),

    /// Corresponding nodes are equal (and we can compare their children).
    Equal(&'a T, &'a T, Vec<Diff<'a, T>>),

    /// Corresponding nodes are not equal.
    Replace(&'a T, &'a T),
}

/// Compute the flat difference between two trees of comparable elements.
///
/// See [`flat_diff_with`](fn.flat_diff_with.html) for an explanation of what _flat_ means.
pub fn flat_diff<'a, T: TreeNode + Eq>(lhs: &'a T, rhs: &'a T) -> Diff<'a, T> {
    flat_diff_with(lhs, rhs, &|lhs, rhs| lhs == rhs)
}

/// Compute the flat difference between two tree using the provided comparator.
///
/// This function computes a _flat_ difference, meaning that it simply compares trees from root
/// to leaves in breadth-first fashion until the first difference is met, and sibling nodes are
/// compared with a sequence diff algorithm. The most prominent implication of all this is that
/// this algorithm fails to notice node movement.
///
/// While such awareness is sometimes desired, it has much more significant computation cost.
/// More precise algorithms for computing tree edit distance (e.g. Zhang-Shasha) have O(n1 * n2)
/// complexity, where n1 and n2 are amounts of nodes in the trees. This algorithm, however, has
/// O((n1 + n2) * (m1 * m2)) complexity, where m1 and m2 are maximum number of child nodes in the
/// trees (which are usually small). Thus it is much more efficient at comparing mostly equivalent
/// syntax trees with minor number of errors. Finally, flat diff is much more suitable for textual
/// presentation, as it captures only horizontal movements of nodes on the same level.
///
/// Example:
///
/// ```plaintext
///         A              A               A
///         |- B           |- B            |- B
///         |  |- D        |  |- E         |  |- (-) D
///         |  |  |- G     |  |- Q         |  |- E
/// diff (  |  |  `- H  ,  |  `- F   )  =  |  |- (+) Q
///         |  |- E        `- C            |  `- F
///         |  `- F           `- D         `- C
///         `- C                 |- G         `- (+) D
///                              |  `- J
///                              `- H
/// ```
pub fn flat_diff_with<'a, T>(lhs: &'a T, rhs: &'a T, equal: &Fn(&T, &T) -> bool) -> Diff<'a, T>
    where T: TreeNode
{
    if equal(lhs, rhs) {
        Diff::Equal(lhs, rhs, flat_child_diff(lhs, rhs, equal))
    } else {
        Diff::Replace(lhs, rhs)
    }
}

fn flat_child_diff<'a, T>(lhs: &'a T, rhs: &'a T, equal: &Fn(&T, &T) -> bool) -> Vec<Diff<'a, T>>
    where T: TreeNode
{
    let lhs_children = lhs.children();
    let rhs_children = rhs.children();

    sequence::diff_with(&lhs_children, &rhs_children, &|lhs, rhs| equal(lhs, rhs))
        .iter()
        .map(|diff| match *diff {
            sequence::Diff::Left(lhs) => {
                self::Diff::Left(*lhs)
            }
            sequence::Diff::Right(rhs) => {
                self::Diff::Right(*rhs)
            }
            sequence::Diff::Replace(lhs, rhs) => {
                self::Diff::Replace(*lhs, *rhs)
            }
            sequence::Diff::Equal(lhs, rhs) => {
                self::Diff::Equal(*lhs, *rhs, flat_child_diff(*lhs, *rhs, equal))
            }
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::ops::Index;
    use utils::tree::{TreeNode};

    #[derive(Debug, Eq)]
    struct Tree<T> {
        value: T,
        children: Vec<Tree<T>>,
    }

    impl<T> PartialEq for Tree<T> where T: PartialEq {
        fn eq(&self, other: &Self) -> bool {
            self.value == other.value
        }
    }

    impl<T> TreeNode for Tree<T> {
        fn children<'a>(&'a self) -> Vec<&'a Self> {
            self.children.iter().collect()
        }
    }

    impl<T> Tree<T> {
        fn new(value: T, children: Vec<Tree<T>>) -> Tree<T> {
            Tree { value: value, children: children }
        }
    }

    impl<T> Index<usize> for Tree<T> {
        type Output = Tree<T>;

        fn index(&self, index: usize) -> &Self::Output {
            &self.children[index]
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Flat diff

    #[test]
    fn root_not_equal() {
        let a = Tree::new(1, vec![]);
        let b = Tree::new(2, vec![]);

        assert_eq!(flat_diff(&a, &b), Diff::Replace(&a, &b));
    }

    #[test]
    fn root_not_equal_children_equal() {
        let a = Tree::new(1, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);
        let b = Tree::new(2, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);

        assert_eq!(flat_diff(&a, &b), Diff::Replace(&a, &b));
    }

    #[test]
    fn root_equal() {
        let a = Tree::new(1, vec![]);
        let b = Tree::new(1, vec![]);

        assert_eq!(flat_diff(&a, &b), Diff::Equal(&a, &b, vec![]));
    }

    #[test]
    fn root_equal_children_equal() {
        let a = Tree::new(1, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);
        let b = Tree::new(1, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);

        assert_eq!(flat_diff(&a, &b),
            Diff::Equal(&a, &b, vec![
                Diff::Equal(&a[0], &b[0], vec![]),
                Diff::Equal(&a[1], &b[1], vec![]),
            ])
        );
    }

    #[test]
    fn children_diff_1() {
        let a = Tree::new(1, vec![Tree::new(2, vec![])]);
        let b = Tree::new(1, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);

        assert_eq!(flat_diff(&a, &b),
            Diff::Equal(&a, &b, vec![
                Diff::Equal(&a[0], &b[0], vec![]),
                Diff::Right(&b[1]),
            ])
        );
    }

    #[test]
    fn children_diff_2() {
        let a = Tree::new(1, vec![Tree::new(2, vec![]), Tree::new(3, vec![])]);
        let b = Tree::new(1, vec![Tree::new(2, vec![])]);

        assert_eq!(flat_diff(&a, &b),
            Diff::Equal(&a, &b, vec![
                Diff::Equal(&a[0], &b[0], vec![]),
                Diff::Left(&a[1]),
            ])
        );
    }

    #[test]
    fn children_diff_3() {
        let a = Tree::new(1, vec![Tree::new(2, vec![])]);
        let b = Tree::new(1, vec![Tree::new(3, vec![])]);

        assert_eq!(flat_diff(&a, &b),
            Diff::Equal(&a, &b, vec![
                Diff::Replace(&a[0], &b[0]),
            ])
        );
    }

    #[test]
    fn children_diff_deep() {
        let a = Tree::new(1, vec![
            Tree::new(2, vec![
                Tree::new(3, vec![
                    Tree::new(4, vec![]),
                ]),
                Tree::new(5, vec![
                    Tree::new(6, vec![]),
                    Tree::new(7, vec![]),
                ]),
                Tree::new(8, vec![
                    Tree::new(9, vec![]),
                    Tree::new(10, vec![]),
                ]),
                Tree::new(11, vec![]),
            ]),
            Tree::new(12, vec![
                Tree::new(13, vec![
                    Tree::new(14, vec![]),
                ]),
            ]),
            Tree::new(15, vec![]),
        ]);
        let b = Tree::new(1, vec![
            Tree::new(2, vec![
                Tree::new(3, vec![
                    Tree::new(4, vec![]),
                    Tree::new(6, vec![]),
                ]),
                Tree::new(5, vec![
                    Tree::new(7, vec![]),
                ]),
                Tree::new(8, vec![
                    Tree::new(9, vec![
                        Tree::new(20, vec![]),
                        Tree::new(21, vec![
                            Tree::new(22, vec![]),
                        ]),
                    ]),
                    Tree::new(10, vec![]),
                ]),
                Tree::new(11, vec![]),
            ]),
            Tree::new(18, vec![]),
            Tree::new(12, vec![
                Tree::new(13, vec![
                    Tree::new(15, vec![]),
                ]),
            ]),
            Tree::new(19, vec![]),
            Tree::new(17, vec![]),
            Tree::new(16, vec![]),
        ]);

        assert_eq!(flat_diff(&a, &b),
            Diff::Equal(&a, &b, vec![
                Diff::Equal(&a[0], &b[0], vec![
                    Diff::Equal(&a[0][0], &b[0][0], vec![
                        Diff::Equal(&a[0][0][0], &b[0][0][0], vec![]),
                        Diff::Right(&b[0][0][1]),
                    ]),
                    Diff::Equal(&a[0][1], &b[0][1], vec![
                        Diff::Left (&a[0][1][0]),
                        Diff::Equal(&a[0][1][1], &b[0][1][0], vec![]),
                    ]),
                    Diff::Equal(&a[0][2], &b[0][2], vec![
                        Diff::Equal(&a[0][2][0], &b[0][2][0], vec![
                            Diff::Right(&b[0][2][0][0]),
                            Diff::Right(&b[0][2][0][1]),
                        ]),
                        Diff::Equal(&a[0][2][1], &b[0][2][1], vec![]),
                    ]),
                    Diff::Equal(&a[0][3], &b[0][3], vec![]),
                ]),
                Diff::Right(&b[1]),
                Diff::Equal(&a[1], &b[2], vec![
                    Diff::Equal(&a[1][0], &b[2][0], vec![
                        Diff::Replace(&a[1][0][0], &b[2][0][0]),
                    ]),
                ]),
                Diff::Right(&b[3]),
                Diff::Right(&b[4]),
                Diff::Replace(&a[2], &b[5]),
            ])
        );
    }
}
