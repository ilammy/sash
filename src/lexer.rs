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

    /// Left (opening) parenthesis `(`
    Lparen,

    /// Right (closing) parenthesis `)`
    Rparen,

    /// Left (opening) bracket `[`
    Lbrack,

    /// Right (closing) bracket `]`
    Rbrack,

    /// Left (opening) brace `{`
    Lbrace,

    /// Right (closing) brace `}`
    Rbrace,

    /// Dot `.`
    Dot,

    /// Comma `,`
    Comma,

    /// Colon `:`
    Colon,

    /// Double colon `::`
    Dualcolon,

    /// Semicolon `;`
    Semicolon,

    /// Integer literal
    Integer,

    /// Float literal
    Float,
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

    /// Peek the character after the next without updating anything
    fn peekpeek(&self) -> Option<char> {
        self.buf[self.pos..].chars().nth(1)
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
            '(' => { self.read(); self.tok = Token::Lparen; }
            ')' => { self.read(); self.tok = Token::Rparen; }
            '[' => { self.read(); self.tok = Token::Lbrack; }
            ']' => { self.read(); self.tok = Token::Rbrack; }
            '{' => { self.read(); self.tok = Token::Lbrace; }
            '}' => { self.read(); self.tok = Token::Rbrace; }
            ',' => { self.read(); self.tok = Token::Comma; }
            ';' => { self.read(); self.tok = Token::Semicolon; }
            '.' => {
                match self.peek() {
                    Some('.') => {
                        panic!("unimplemented"); // identifiers
                    }
                    _ => {
                        self.read();
                        self.tok = Token::Dot;
                    }
                }
            }
            ':' => {
                self.read();
                match self.cur {
                    Some(':') => {
                        self.read();
                        self.tok = Token::Dualcolon;
                    }
                    _ => {
                        self.tok = Token::Colon;
                    }
                }
            }
            '0'...'9' => {
                self.scan_number();
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

    /// Scan over any number
    fn scan_number(&mut self) {
        // Okay, first of all, numbers start with a decimal digit
        assert!(StringScanner::is_digit(self.cur.unwrap(), 10));

        // And then they have some digits as their integer part
        let (base, digits) = match self.cur.unwrap() {
            '0' => {
                self.read();
                match self.cur.unwrap_or('\0') {
                    // "0b...", "0o...", "0x..." are non-decimal prefixes
                    'b' => { self.read(); (2,  self.scan_digits( 2, 10)) }
                    'o' => { self.read(); (8,  self.scan_digits( 8, 10)) }
                    'x' => { self.read(); (16, self.scan_digits(16, 16)) }

                    // Don't forget about that one zero we have already seen
                    _ => { (10, self.scan_digits(10, 10) + 1) }
                }
            }
            '1'...'9' => { (10, self.scan_digits(10, 10)) }

            _ => { unreachable!(); }
        };

        // The integer part may contain no valid digits, like in "0o999" or "0x__"
        if digits == 0 {
            self.report.error(Span::new(self.start, self.prev_pos),
                "The number contains no valid digits");
        }

        // According to what we have seen up to this point, it is integer
        self.tok = Token::Integer;

        // Though, a dot after an integer may mark a floating-point literal...
        if self.cur == Some('.') {
            let c = self.peek().unwrap_or('\0');

            // ... if it is followed by another (decimal) integer
            if StringScanner::is_digit(c, 10) || c == '_' {
                self.read();
                self.scan_float_fractional_part();
                self.tok = Token::Float;
            } else {
                // Else it is just an integer followed by some dot. While dots can form identifiers
                // (like '...'), type suffixes are defined as word-identifiers, which dots aren't.
                // Thus we just go out with the suffixless integer we have already scanned over.
                return;
            }
        }

        // An 'e' may start either a floating-point exponent, or (technically) a type suffix.
        // This is ambiguous, so we resolve it by greedily favoring the exponent treatment.
        if self.cur == Some('e') || self.cur == Some('E') {
            let c = self.peek().unwrap_or('\0');

            if StringScanner::is_digit(c, 10) || c == '_' {
                // An 'e' followed by a number is an exponent
                self.read();
                self.scan_float_exponent();
                self.tok = Token::Float;
            } else if c == '+' || c == '-' {
                // An 'e' followed by a sign which is followed by a number is an exponent.
                // If the sign is not followed by a number then we've seen just a suffix "e"
                // with '+' or '-' being a part of some symbol-identifier that follows.
                let c = self.peekpeek().unwrap_or('\0');

                if StringScanner::is_digit(c, 10) || c == '_' {
                    self.read();
                    self.read();
                    self.scan_float_exponent();
                    self.tok = Token::Float;
                }
            } else {
                // Not an exponent, just some (invalid) type suffix starting with 'e'.
                // But we are in lexer and have no idea about is validity, so we go along.
            }
        }

        // TODO: attempt to scan over a suffix

        // Some late check for floating-point base. We do not support binary literals for floats.
        if (self.tok == Token::Float) && (base != 10) {
            self.report.error(Span::new(self.start, self.prev_pos),
                "Float number must be decimal");
        }
    }

    /// Scan over a sequence of digits
    ///
    /// Digits of `base` are valid. Digits of `allowed` base are scanned over,
    /// but they are reported as erroneous if they are not fitting for `base`.
    /// Also scans over any digit separators `_`.
    ///
    /// Returns a number of actual digits scanned (not counting the separators).
    fn scan_digits(&mut self, base: u32, allowed: u32) -> usize {
        assert!(base <= allowed);

        let mut digits = 0;

        while !self.at_eof() {
            let c = self.cur.unwrap();

            if c != '_' {
                if !StringScanner::is_digit(c, base) {
                    if StringScanner::is_digit(c, allowed) {
                        self.report.error(Span::new(self.prev_pos, self.pos),
                            "Unexpected digit"); // TODO: better message
                    } else {
                        break;
                    }
                }
                digits += 1;
            }

            self.read();
        }

        return digits;
    }

    /// Check whether `c` is a valid digit of base `base`
    fn is_digit(c: char, base: u32) -> bool {
        match base {
             2 => {  ('0' <= c) && (c <= '1') }
             8 => {  ('0' <= c) && (c <= '7') }
            10 => {  ('0' <= c) && (c <= '9') }
            16 => { (('0' <= c) && (c <= '9')) ||
                    (('a' <= c) && (c <= 'f')) ||
                    (('A' <= c) && (c <= 'F')) }
             _ => { panic!("invalid numeric base {}", base); }
        }
    }

    /// Scan over a fractional part of a floating-point literal
    fn scan_float_fractional_part(&mut self) {
        assert!(StringScanner::is_digit(self.cur.unwrap(), 10) || self.cur == Some('_'));

        let fractional_start = self.prev_pos;
        let fractional_digits = self.scan_digits(10, 10);

        if fractional_digits == 0 {
            self.report.error(Span::new(fractional_start, self.prev_pos),
                "The fractional part contains no valid digits");
        }
    }

    /// Scan over an exponent part of a floating-point literal
    fn scan_float_exponent(&mut self) {
        assert!(StringScanner::is_digit(self.cur.unwrap(), 10) || self.cur == Some('_'));

        let exponent_start = self.prev_pos;
        let exponent_digits = self.scan_digits(10, 10);

        if exponent_digits == 0 {
            self.report.error(Span::new(exponent_start, self.prev_pos),
                "The exponent contains no valid digits");
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
    // Brackets and other fixed tokens

    #[test]
    fn brackets() {
        check(&[
            ScannerTestSlice("(",    Token::Lparen),
            ScannerTestSlice("]",    Token::Rbrack),
            ScannerTestSlice("\n\n", Token::Whitespace),
            ScannerTestSlice("}",    Token::Rbrace),
            ScannerTestSlice("}",    Token::Rbrace),
            ScannerTestSlice(" ",    Token::Whitespace),
            ScannerTestSlice("[",    Token::Lbrack),
            ScannerTestSlice("[",    Token::Lbrack),
            ScannerTestSlice("\t",   Token::Whitespace),
            ScannerTestSlice("(",    Token::Lparen),
            ScannerTestSlice("{",    Token::Lbrace),
            ScannerTestSlice("\r\n", Token::Whitespace),
            ScannerTestSlice(")",    Token::Rparen),
            ScannerTestSlice(")",    Token::Rparen),
        ], &[], &[]);
    }

    #[test]
    fn punctuation() {
        check(&[
            ScannerTestSlice(",",  Token::Comma),
            ScannerTestSlice(".",  Token::Dot),
            ScannerTestSlice("::", Token::Dualcolon),
            ScannerTestSlice(".",  Token::Dot),
            ScannerTestSlice(":",  Token::Colon),
            ScannerTestSlice(" ",  Token::Whitespace),
            ScannerTestSlice(":",  Token::Colon),
            ScannerTestSlice(".",  Token::Dot),
            ScannerTestSlice(";",  Token::Semicolon),
            ScannerTestSlice("(",  Token::Lparen),
            ScannerTestSlice(";",  Token::Semicolon),
            ScannerTestSlice(";",  Token::Semicolon),
            ScannerTestSlice(",",  Token::Comma),
            ScannerTestSlice(",",  Token::Comma),
        ], &[], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Integers

    #[test]
    fn integer_basic_decimal() {
        check(&[
            ScannerTestSlice("0",     Token::Integer),
            ScannerTestSlice(",",     Token::Comma),
            ScannerTestSlice("1",     Token::Integer),
            ScannerTestSlice(",",     Token::Comma),
            ScannerTestSlice("00000", Token::Integer),
            ScannerTestSlice(",",     Token::Comma),
            ScannerTestSlice("00001", Token::Integer),
            ScannerTestSlice(",",     Token::Comma),
            ScannerTestSlice(" ",     Token::Whitespace),
            ScannerTestSlice("42",    Token::Integer),
            ScannerTestSlice(" ",     Token::Whitespace),
            ScannerTestSlice("9137847823642354637463430", Token::Integer),
            ScannerTestSlice("\n",    Token::Whitespace),
            ScannerTestSlice("(",     Token::Lparen),
            ScannerTestSlice("12345", Token::Integer),
            ScannerTestSlice(")",     Token::Rparen),
            ScannerTestSlice("67890", Token::Integer),
        ], &[], &[]);
    }

    #[test]
    fn integer_basic_nondecimal() {
        check(&[
            ScannerTestSlice("0b0110101010",    Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0o755",           Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0o32",            Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0o0",             Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0xDBE",           Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0x12345",         Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0xDeadBeef",      Token::Integer),
            ScannerTestSlice(",",               Token::Comma),
            ScannerTestSlice("0xAAAAAAAAAAAAA", Token::Integer),
        ], &[], &[]);
    }

    #[test]
    fn integer_separators() {
        check(&[
            ScannerTestSlice("0___",       Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("10_000",     Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("1_2_3_4_5",  Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("0x__5__",    Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("0b_0_1_1_0", Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("0o_7_7_7_",  Token::Integer),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("0________0", Token::Integer),
        ], &[], &[]);
    }

    #[test]
    fn integer_unexpected_digit_range() {
        check(&[
            ScannerTestSlice("0b12345", Token::Integer),
            ScannerTestSlice(",",       Token::Comma),
            ScannerTestSlice("0o48_19", Token::Integer),
            // There are no unexpected characters in decimal or hexadecimal literals.            // The first nondigit is either the start of a type suffix, or the first
            // character of the next token.
        ], &[ Span::new(3, 4), Span::new(4, 5), Span::new(5, 6), Span::new(6, 7),
              Span::new(11, 12), Span::new(14, 15)], &[]);
    }

    #[test]
    fn integer_unexpected_nondecimal_termination() {
        check(&[
            ScannerTestSlice("0x",  Token::Integer),
            ScannerTestSlice(",",   Token::Comma),
            ScannerTestSlice("0b",  Token::Integer),
            ScannerTestSlice(",",   Token::Comma),
            ScannerTestSlice("0o",  Token::Integer),
            ScannerTestSlice(",",   Token::Comma),
            ScannerTestSlice("0x_", Token::Integer),
            ScannerTestSlice(",",   Token::Comma),
            ScannerTestSlice("0b_", Token::Integer),
            ScannerTestSlice(",",   Token::Comma),
            ScannerTestSlice("0o_", Token::Integer),
        ], &[ Span::new(0, 2), Span::new(3, 5), Span::new(6, 8), Span::new(9, 12),
              Span::new(13, 16), Span::new(17, 20) ], &[]);
    }

    // TODO: combined errors

    // TODO: type suffixes
    //   correct suffixes
    //   0g42 parses as 0 + g42, not as incorrect radix spec
    //   0b22 is incorrect digits
    //   0_b22 is (lexically) correct suffix

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Floats

    #[test]
    fn float_basic() {
        check(&[
            ScannerTestSlice("0.0",             Token::Float),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("1.0",             Token::Float),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("12313.123123121", Token::Float),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("0.0000000005",    Token::Float),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("0000000.1200000", Token::Float),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("56.43453",        Token::Float),
        ], &[], &[]);
    }

    #[test]
    fn float_exponential_without_dot() {
        check(&[
            ScannerTestSlice("9e10",        Token::Float),
            ScannerTestSlice(",",           Token::Comma),
            ScannerTestSlice("1400e+12313", Token::Float),
            ScannerTestSlice(",",           Token::Comma),
            ScannerTestSlice("1400E-2323",  Token::Float),
            ScannerTestSlice("//\n",        Token::Comment),
            ScannerTestSlice("0e+0",        Token::Float),
            ScannerTestSlice(",",           Token::Comma),
            ScannerTestSlice("0001E1000",   Token::Float),
            ScannerTestSlice(",",           Token::Comma),
            ScannerTestSlice("0e-0",        Token::Float),
        ], &[], &[]);
    }

    #[test]
    fn float_exponential_with_dot() {
        check(&[
            ScannerTestSlice("2.0E10",           Token::Float),
            ScannerTestSlice(")",                Token::Rparen),
            ScannerTestSlice("0.00000e0",        Token::Float),
            ScannerTestSlice("[",                Token::Lbrack),
            ScannerTestSlice("123.456e+789",     Token::Float),
            ScannerTestSlice("}",                Token::Rbrace),
            ScannerTestSlice("11.11E-11",        Token::Float),
            ScannerTestSlice("{",                Token::Lbrace),
            ScannerTestSlice("9363.83929e00434", Token::Float),
        ], &[], &[]);
    }

    #[test]
    fn float_extreme() {
        // Just making sure that scanner does not care about semantics
        check(&[
            ScannerTestSlice("999999999999999999999999.999999999999999999", Token::Float),
            ScannerTestSlice("\r\n",                                        Token::Whitespace),
            ScannerTestSlice("0.0000000000000000000e-99999999999999999999", Token::Float),
            ScannerTestSlice("\r\n",                                        Token::Whitespace),
            ScannerTestSlice("1.2345678901234567890E+12345678901234567890", Token::Float),
            ScannerTestSlice("\r\n",                                        Token::Whitespace),
            ScannerTestSlice("12345678.901234567890E123456789012345678901", Token::Float),
        ], &[], &[]);
    }

    #[test]
    fn float_separators() {
        check(&[
            ScannerTestSlice("10_000.000_001", Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("0______0.5",     Token::Float),
            ScannerTestSlice(":",              Token::Colon),
            ScannerTestSlice("1_._2",          Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("3._4_",          Token::Float),
            ScannerTestSlice(":",              Token::Colon),
            ScannerTestSlice("7___e54",        Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("3_._1_E_4",      Token::Float),
            ScannerTestSlice(":",              Token::Colon),
            ScannerTestSlice("0.0e+___4",      Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("0._0E-__5__",    Token::Float),
        ], &[], &[]);
    }

    #[test]
    fn float_deny_radix_spec() {
        check(&[
            ScannerTestSlice("0b1e101101",         Token::Float),
            ScannerTestSlice("          ",         Token::Whitespace),
            ScannerTestSlice("0b01011011.0110101", Token::Float),
            ScannerTestSlice("/*      */",         Token::Comment),
            ScannerTestSlice("0o7.7",              Token::Float),
            ScannerTestSlice("          ",         Token::Whitespace),
            ScannerTestSlice("0o77e10",            Token::Float),
            ScannerTestSlice("          ",         Token::Whitespace),
            ScannerTestSlice("0x00.0E7",           Token::Float),
            ScannerTestSlice("          ",         Token::Whitespace),
            ScannerTestSlice("0x5.1",              Token::Float),
            ScannerTestSlice("          ",         Token::Whitespace),
            ScannerTestSlice("0o5e+3",             Token::Float),
        ], &[ Span::new(0, 10), Span::new(20, 38), Span::new(48, 53), Span::new(63, 70),
              Span::new(80, 88), Span::new(98, 103), Span::new(113, 119) ], &[]);
    }

    #[test]
    fn float_missing_numbers() {
        check(&[
            ScannerTestSlice("5._____",        Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("0._",            Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("1e___",          Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("5.0E+___",       Token::Float),
            ScannerTestSlice(",",              Token::Comma),
            ScannerTestSlice("10e-___",        Token::Float),
        ], &[ Span::new(2, 7), Span::new(10, 11), Span::new(14, 17),
              Span::new(23, 26), Span::new(31, 34) ], &[]);
    }

    // TODO: combined errors

    // TODO: type suffixes

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
