// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

use std::mem;

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Helper data structures
//

/// Tokens recognized by the scanner
#[derive(Debug, PartialEq)]
pub enum Token {
    /// Marker token denoting the end-of-token-stream condition
    EOF,

    /// Non-significant whitespace
    Whitespace,

    /// Non-significant comment
    Comment,
}

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
    fn new(from: usize, to: usize) -> Span {
        assert!(from <= to);
        Span { from: from, to: to }
    }
}

/// Scanned token with extents information
pub struct ScannedToken {
    /// The token itself
    pub tok: Token,

    /// Span of the token
    pub span: Span,
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Diagnostic reporting
//

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

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// The scanner
//

/// Scanner interface
///
/// A scanner splits a string of characters into tokens. It does not process the characters it
/// sees; it only recognizes the tokens and provides their general category and extents in the
/// string. Being that stupid, the scanner is single-pass and does not provide any backtracking
/// for error recovery. If a token seems to be malformed the scanner will do its best to guess
/// the intended meaning, report any encountered errors, and will carry on scanning if possible.
/// However, a scanner will never reconsider its decisions about what it saw and where it was.
pub trait Scanner<'a> {
    /// Check whether the end of token stream has been reached.
    /// If it is reached, the scanner will produce only `Token::EOF`.
    fn at_eof(&self) -> bool;

    /// Extract the next token from the stream.
    fn next_token(&mut self) -> ScannedToken;
}

/// A scanner for strings
pub struct StringScanner<'a> {
    /// The string being scanned
    buf: &'a str,

    // Scanning state
    //
    //     buf
    //     ----+---+---+---+-----+---+---+---+---+-----+---+---+---+
    //     ... | f | o | o | ... | b |   ä   | r | ... | e | n | d |
    //     ----+---+---+---+-----+---+---+---+---+-----+---+---+---+
    //          ^   ^                 ^       ^                     ^
    //          |   pos               |       pos                   pos, prev_pos
    //          |                     |
    //          prev_pos              prev_pos
    //
    //     cur == Some('f')           cur == Some('ä')              cur == None

    /// Most recently read character (located at `prev_pos` in the stream)
    cur: Option<char>,

    /// Byte offset of the next character to be read (after `cur`)
    pos: usize,

    /// Byte offset of the last character that was read (`cur`)
    prev_pos: usize,

    // Temporaries for the token currently being scanned

    /// The token to be returned
    tok: Token,

    /// First character of `tok`
    start: usize,

    /// Last character of `tok`
    end: usize,

    // Diagnostic reporting

    /// Our designed responsible for diagnostic processing
    report: &'a SpanReporter<'a>,
}

impl<'a> Scanner<'a> for StringScanner<'a> {
    fn at_eof(&self) -> bool {
        self.cur.is_none()
    }

    fn next_token(&mut self) -> ScannedToken {
        self.next();

        ScannedToken {
            tok: mem::replace(&mut self.tok, Token::EOF),
            span: Span::new(self.start, self.end),
        }
    }
}

impl<'a> StringScanner<'a> {
    /// Make a new scanner for a given string
    pub fn new<'b>(s: &'b str, reporter: &'b SpanReporter<'b>) -> StringScanner<'b> {
        let mut scanner = StringScanner {
            buf: s,
            cur: None, pos: 0, prev_pos: 0,
            tok: Token::EOF, start: 0, end: 0,
            report: reporter,
        };
        scanner.read();
        scanner
    }

    /// Read the next character and update `cur`, `pos`, `prev_pos`
    fn read(&mut self) {
        self.prev_pos = self.pos;
        self.cur = self.peek();
        match self.cur {
            Some(c) => { self.pos += c.len_utf8(); }
            None    => { }
        }
    }

    /// Peek the next character without updating anything
    fn peek(&self) -> Option<char> {
        self.buf[self.pos..].chars().nth(0)
    }

    /// Scan the next token from the stream and set `tok`, `span`, `errors`
    fn next(&mut self) {
        if self.at_eof() {
            self.tok = Token::EOF;
            self.start = self.pos;
            self.end = self.pos;
            return;
        }

        self.tok = Token::EOF;

        self.start = self.prev_pos;

        match self.cur.unwrap() {
            ' ' | '\t' | '\n' | '\r' => {
                self.scan_whitespace();
            }
            '/' => {
                match self.peek() {
                    Some('/') => {
                        self.scan_line_comment();
                    }
                    Some('*') => {
                        self.scan_block_comment();
                    }
                    _ => { panic!("unimplemented"); }
                }
            }
            _ => { panic!("unimplemented"); }
        }

        self.end = self.prev_pos;

        assert!(self.tok != Token::EOF);
    }

    /// Scan over a sequence of whitespace
    fn scan_whitespace(&mut self) {
        while !self.at_eof() {
            match self.cur.unwrap() {
                ' ' | '\t' | '\n' | '\r' => { self.read(); }
                _                        => { break; }
            }
        }
        self.tok = Token::Whitespace;
    }

    /// Scan over a line comment
    fn scan_line_comment(&mut self) {
        assert!(self.cur == Some('/') && self.peek() == Some('/'));
        self.read();
        self.read();

        while !self.at_eof() {
            match self.cur.unwrap() {
                '\n' => {
                    self.read();
                    break;
                }
                '\r' => {
                    match self.peek() {
                        Some('\n') => {
                            self.read();
                            self.read();
                            break;
                        }
                        _ => {
                            self.report.warning(Span::new(self.prev_pos, self.pos),
                                "Bare CR character encountered in a line comment. \
                                 Did you mean Windows line ending, CRLF?");

                            self.read();
                        }
                    }
                }
                _ => { self.read(); }
            }
        }
        self.tok = Token::Comment;
    }

    /// Scan a block comment.
    fn scan_block_comment(&mut self) {
        assert!(self.cur == Some('/') && self.peek() == Some('*'));
        self.read();
        self.read();

        let mut nesting_level = 1;

        while !self.at_eof() {
            match self.cur.unwrap() {
                '*' => {
                    self.read();
                    match self.cur {
                        Some('/') => {
                            self.read();
                            nesting_level -= 1;
                            if nesting_level == 0 {
                                break;
                            }
                        }
                        _ => { }
                    }
                }
                '/' => {
                    self.read();
                    match self.cur {
                        Some('*') => {
                            self.read();
                            nesting_level += 1;
                        }
                        _ => { }
                    }
                }
                _ => { self.read(); }
            }
        }

        self.tok = Token::Comment;

        if nesting_level > 0 {
            self.report.error(Span::new(self.start, self.pos),
                "Unexpected end of file while reading a block comment. \
                 Please look for the missing block comment closure */");

            self.tok = Token::Comment;
        }
    }
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Tests
//

#[cfg(test)]
mod tests {
    use super::*;

    // TODO: macros to lower the amount of boilerplate and arbitrary calculations

    #[test]
    fn empty_string() {
        check(&[], &[], &[]);
    }

    #[test]
    fn whitespace() {
        check(&[
            ScannerTestSlice("   \t\t\r\n  \t \t\n", Token::Whitespace),
        ], &[], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Line comments

    #[test]
    fn line_comment_lf() {
        check(&[
            ScannerTestSlice("// example line comment\n", Token::Comment),
            ScannerTestSlice("       \t",                 Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn line_comment_crlf() {
        check(&[
            ScannerTestSlice("// example line comment\r\n", Token::Comment),
            ScannerTestSlice("       \t",                   Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn line_comment_cr() {
        check(&[
            ScannerTestSlice("// example line comment\r       \t", Token::Comment),
        ], &[], &[Span::new(23, 24)]);
    }

    #[test]
    fn line_comment_consecutive_lf() {
        check(&[
            ScannerTestSlice("// line 1\n", Token::Comment),
            ScannerTestSlice("// line 2\n", Token::Comment),
            ScannerTestSlice("     ",       Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn line_comment_consecutive_crlf() {
        check(&[
            ScannerTestSlice("// line 1\r\n", Token::Comment),
            ScannerTestSlice("// line 2\r\n", Token::Comment),
            ScannerTestSlice("     ",         Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn line_comment_consecutive_cr() {
        check(&[
            ScannerTestSlice("// line 1\r// line 2\r     ", Token::Comment),
        ], &[], &[Span::new(9, 10), Span::new(19, 20)]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Block comments

    #[test]
    fn block_comment_simple() {
        check(&[
            ScannerTestSlice("/* example */", Token::Comment),
        ], &[], &[]);
    }

    #[test]
    fn block_comment_multiline() {
        check(&[
            ScannerTestSlice("/* example\non the next line */", Token::Comment),
        ], &[], &[]);
    }

    #[test]
    fn block_comment_nested() {
        check(&[
            ScannerTestSlice("/* /* nested */ example /**/*/", Token::Comment),
        ], &[], &[]);
    }

    #[test]
    fn block_comment_consecutive() {
        check(&[
            ScannerTestSlice("/*1*/", Token::Comment),
            ScannerTestSlice("\n",    Token::Whitespace),
            ScannerTestSlice("/*2*/", Token::Comment),
        ], &[], &[]);
    }

    #[test]
    fn block_comment_unterminated_1() {
        check(&[
            ScannerTestSlice("/* forgot", Token::Comment),
        ], &[Span::new(0, 9)], &[]);
    }

    #[test]
    fn block_comment_unterminated_2() {
        check(&[
            ScannerTestSlice("/*/", Token::Comment),
        ], &[Span::new(0, 3)], &[]);
    }

    #[test]
    fn block_comment_unterminated_nested() {
        check(&[
            ScannerTestSlice("/*/*nested*/", Token::Comment),
        ], &[Span::new(0, 12)], &[]);
    }

    #[test]
    fn block_comment_line_comment_allows_unterminated_blocks() {
        check(&[
            ScannerTestSlice("// /* doesn't matter", Token::Comment),
        ], &[], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Test helpers

    use std::cell::RefCell;

    struct ScannerTestSlice<'a>(&'a str, Token);

    struct SinkReporter<'a> {
        pub errors: RefCell<Vec<(Span, &'a str)>>,
        pub warnings: RefCell<Vec<(Span, &'a str)>>,
    }

    impl<'a> SpanReporter<'a> for SinkReporter<'a> {
        fn error(&self, span: Span, message: &'a str) {
            self.errors.borrow_mut().push((span, message));
        }

        fn warning(&self, span: Span, message: &'a str) {
            self.warnings.borrow_mut().push((span, message));
        }
    }

    impl<'a> SinkReporter<'a> {
        fn new<'b>() -> SinkReporter<'b> {
            SinkReporter {
                errors: RefCell::new(Vec::new()),
                warnings: RefCell::new(Vec::new()),
            }
        }
    }

    fn check(slices: &[ScannerTestSlice], error_spans: &[Span], warning_spans: &[Span]) {
        let whole_string = {
            let mut t = String::new();
            for &ScannerTestSlice(s, _) in slices {
                t.push_str(s);
            }
            t
        };
        let end = whole_string.len();

        let mut tok_iter = 1;
        let mut byte_iter = 0;

        let sink = SinkReporter::new();

        let mut scanner = StringScanner::new(whole_string.as_ref(), &sink);

        for &ScannerTestSlice(s, ref t) in slices {
            check_token(&scanner.next_token(), tok_iter, t,
                        &Span::new(byte_iter, byte_iter + s.len()));

            tok_iter += 1;
            byte_iter += s.len();
        }

        check_token(&scanner.next_token(), tok_iter, &Token::EOF, &Span::new(end, end));

        check_spans("errors", error_spans, &sink.errors.borrow()[..]);
        check_spans("warnings", warning_spans, &sink.warnings.borrow()[..]);
    }

    fn check_token(scanned: &ScannedToken, idx: u32, kind: &Token, span: &Span) {
        if (scanned.tok == *kind) && (scanned.span == *span) {
            return;
        }
        panic!("assertion failed: expected token #{} to be {:?}{} at {:?}{}",
               idx,
               *kind, if scanned.tok == *kind {
                   String::new()
               } else {
                   format!(" (got {:?})", scanned.tok)
               },
               *span, if scanned.span == *span {
                   String::new()
               } else {
                   format!(" (got {:?})", scanned.span)
               }
        );
    }

    fn check_spans(kind: &str, expected: &[Span], actual: &[(Span, &str)]) {
        if (expected.len() == 0) && (actual.len() > 0) {
            panic!("assertion failed: expected no {}, but got {} of them", kind, actual.len());
        }

        // TODO: better report message and functional implementation

        assert_eq!(expected.len(), actual.len());

        for i in 0..expected.len() {
            assert_eq!(expected[i], actual[i].0);
        }
    }
}
