// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash lexical analyzer.
//!
//! This module contains definition and implementation of the _lexical analyzer_ which breaks
//! a stream of characters into tokens.

use std::char;

use tokens::{Token, Delimiter, Lit};
use diagnostics::{Span, SpanReporter};
use intern_pool::{Atom, InternPool};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Helper data structures
//

/// A scanned token with extents information.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct ScannedToken {
    /// The token itself.
    pub tok: Token,

    /// Span of the token.
    pub span: Span,
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// The scanner
//

/// Scanner interface.
///
/// A scanner splits a string of characters into tokens. It does not process the characters it
/// sees; it only recognizes the tokens and provides their general category and extents in the
/// string. Being that stupid, the scanner is single-pass and does not provide any backtracking
/// for error recovery. If a token seems to be malformed the scanner will do its best to guess
/// the intended meaning, report any encountered errors, and will carry on scanning if possible.
/// However, a scanner will never reconsider its decisions about what it saw and where it was.
pub trait Scanner {
    /// Checks whether the end of token stream has been reached.
    /// If it is reached, the scanner will produce only `Token::EOF`.
    fn at_eof(&self) -> bool;

    /// Extracts and returns the next token from the stream. Returns `Token::EOF`
    /// if the end of stream has been reached and no more tokens are available.
    fn next_token(&mut self) -> ScannedToken;
}

/// A scanner for strings.
pub struct StringScanner<'a> {
    /// The string being scanned.
    buf: &'a str,

    /// The intern pool for atoms stored in scanned tokens.
    pool: &'a InternPool,

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

    /// Most recently read character (located at `prev_pos` in the stream).
    cur: Option<char>,

    /// Byte offset of the next character to be read (after `cur`).
    pos: usize,

    /// Byte offset of the last character that was read (`cur`).
    prev_pos: usize,

    //
    // Temporaries for the token currently being scanned
    //

    /// First character of `tok`.
    start: usize,

    /// Last character of `tok`.
    end: usize,

    //
    // Diagnostic reporting
    //

    /// Our designated responsible for diagnostic processing.
    report: &'a SpanReporter,
}

impl<'a> Scanner for StringScanner<'a> {
    fn at_eof(&self) -> bool {
        self.cur.is_none()
    }

    fn next_token(&mut self) -> ScannedToken {
        self.next()
    }
}

impl<'a> StringScanner<'a> {
    /// Makes a new scanner for the given string which will report scanning errors
    /// to the given reporter and intern strings into the given pool.
    pub fn new(s: &'a str, pool: &'a InternPool, reporter: &'a SpanReporter) -> StringScanner<'a> {
        let mut scanner = StringScanner {
            buf: s,
            pool: pool,
            cur: None, pos: 0, prev_pos: 0,
            start: 0, end: 0,
            report: reporter,
        };
        scanner.read();
        scanner
    }

    /// Read the next character and update `cur`, `pos`, `prev_pos`.
    fn read(&mut self) {
        self.prev_pos = self.pos;
        self.cur = self.peek();
        match self.cur {
            Some(c) => { self.pos += c.len_utf8(); }
            None    => { }
        }
    }

    /// Undo a read and put a character back into `cur` buffer.
    ///
    /// This method is used by identifier scanning code to properly deal with Unicode escapes
    /// without scanning over them several times. It can only unread a single most recently read
    /// character. Think twice before using this method elsewhere.
    fn unread(&mut self, c: char, prev_pos: usize) {
        self.cur = Some(c);
        self.pos = self.prev_pos;
        self.prev_pos = prev_pos;
    }

    /// Peek the next character without updating anything.
    fn peek(&self) -> Option<char> {
        self.buf[self.pos..].chars().nth(0)
    }

    /// Peek the character after the next one without updating anything.
    fn peekpeek(&self) -> Option<char> {
        self.buf[self.pos..].chars().nth(1)
    }

    /// Skip over an expected sequence of characters.
    fn expect_and_skip(&mut self, expected: &str) {
        assert!(self.buf[self.prev_pos..].starts_with(expected));
        for _ in 0..expected.len() { self.read(); }
    }

    /// Check whether current character (`cur`) is `c`.
    fn cur_is(&self, c: char) -> bool {
        self.cur == Some(c)
    }

    /// Check whether next character (`peek()`) is `c`.
    fn peek_is(&self, c: char) -> bool {
        self.peek() == Some(c)
    }

    /// Interns a slice of `buf` into the intern pool.
    fn intern_slice(&self, from: usize, to: usize) -> Atom {
        let slice = &self.buf[from..to];
        return self.pool.intern(slice);
    }

    /// Interns a given string into the intern pool.
    fn intern_string(&self, str: String) -> Atom {
        return self.pool.intern_string(str);
    }

    /// Extract the next token from the stream.
    fn next(&mut self) -> ScannedToken {
        if self.at_eof() {
            return ScannedToken {
                tok: Token::EOF,
                span: Span::new(self.pos, self.pos)
            };
        }

        self.start = self.prev_pos;
        let tok = self.scan_token();
        self.end = self.prev_pos;

        assert!(tok != Token::EOF);

        return ScannedToken {
            tok: tok,
            span: Span::new(self.start, self.end)
        };
    }

    /// Scan over the next token.
    fn scan_token(&mut self) -> Token {
        assert!(!self.at_eof());

        match self.cur.unwrap() {
            ' ' | '\t' | '\n' | '\r' => {
                self.scan_whitespace()
            }
            '/' if self.peek_is('/') => {
                self.scan_line_comment()
            }
            '/' if self.peek_is('*') => {
                self.scan_block_comment()
            }
            '(' => { self.read(); Token::OpenDelim(Delimiter::Paren) }
            '[' => { self.read(); Token::OpenDelim(Delimiter::Bracket) }
            '{' => { self.read(); Token::OpenDelim(Delimiter::Brace) }
            ')' => { self.read(); Token::CloseDelim(Delimiter::Paren) }
            ']' => { self.read(); Token::CloseDelim(Delimiter::Bracket) }
            '}' => { self.read(); Token::CloseDelim(Delimiter::Brace) }
            ',' => { self.read(); Token::Comma }
            ';' => { self.read(); Token::Semicolon }
            '#' => { self.read(); Token::Hash }
            '.' if self.peek() != Some('.') => {
                self.read();
                Token::Dot
            }
            ':' => {
                self.read();
                match self.cur {
                    Some(':') => {
                        self.read();
                        Token::Dualcolon
                    }
                    _ => {
                        Token::Colon
                    }
                }
            }
            '0'...'9' => {
                self.scan_number()
            }
            '\'' => {
                self.scan_character_literal()
            }
            '"' => {
                self.scan_string()
            }
            '`' => {
                self.scan_explicit_symbol()
            }
            'r' => {
                match self.scan_raw_string_leaders() {
                    Some(hashes) => {
                        self.scan_raw_string(hashes)
                    }
                    None => {
                        self.scan_identifier_word_or_symbol('r')
                    }
                }
            }
            _ => {
                self.scan_identifier_or_symbol()
            }
        }
    }

    /// Scan over a sequence of whitespace.
    fn scan_whitespace(&mut self) -> Token {
        while !self.at_eof() {
            match self.cur.unwrap() {
                ' ' | '\t' | '\n' | '\r' => { self.read(); }
                _                        => { break; }
            }
        }
        return Token::Whitespace;
    }

    /// Scan over a line comment.
    fn scan_line_comment(&mut self) -> Token {
        // Line comments start with two consecutive slashes
        self.expect_and_skip("//");

        // '///' and '//!' indicate documentation comments, but '////...' does not.
        let doc_comment = self.cur_is('!') || (self.cur_is('/') && !self.peek_is('/'));

        while !self.at_eof() {
            match self.cur.unwrap() {
                // Stop scanning at the first line ending, no matter what
                '\n' => {
                    break;
                }
                '\r' if self.peek_is('\n') => {
                    break;
                }
                // Report bare CR characters as they may have meant to be line endings,
                // but are not treated as such in Sash.
                '\r' => {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "bare CR is not allowed in line comments");
                    self.read();
                }
                // Skip over anything else, we're scanning a comment
                _ => { self.read(); }
            }
        }

        return if doc_comment {
            Token::DocComment(self.intern_slice(self.start, self.prev_pos))
        } else { Token::Comment };
    }

    /// Scan a block comment.
    fn scan_block_comment(&mut self) -> Token {
        // Block comments start with a slash followed by an asterisk
        self.expect_and_skip("/*");

        // '/**' and '/*!' indicate documentation comments, but '/***...' does not.
        // Also take care to treat '/**/' as a regular comment.
        let doc_comment = self.cur_is('!') ||
            (self.cur_is('*') && !self.peek_is('*') && !self.peek_is('/'));

        let mut nesting_level = 1;

        while !self.at_eof() {
            match self.cur.unwrap() {
                // Block closure, scan over it and maybe stop scanning the comment
                '*' if self.peek_is('/') => {
                    self.read();
                    self.read();
                    nesting_level -= 1;
                    if nesting_level == 0 {
                        break;
                    }
                }
                // A new block is opened, scan over it and bump the nesting level
                '/' if self.peek_is('*') => {
                    self.read();
                    self.read();
                    nesting_level += 1;
                }
                // Report bare CR characters as they may have meant to be line endings,
                // but are not treated as such in Sash.
                '\r' if doc_comment && !self.peek_is('\n') => {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "bare CR is not allowed in documentation comments");
                    self.read();
                }
                // Skip over anything else, we're scanning a comment
                _ => { self.read(); }
            }
        }

        if nesting_level > 0 {
            if doc_comment {
                self.report.fatal(Span::new(self.start, self.prev_pos),
                    "unterminated block comment, expected '*/'");
            } else {
                self.report.fatal(Span::new(self.start, self.prev_pos),
                    "unterminated documentation comment, expected '*/'");
            }

            return Token::Unrecognized;
        }

        return if doc_comment {
            Token::DocComment(self.intern_slice(self.start, self.prev_pos))
        } else { Token::Comment };
    }

    /// Scan over any number literal.
    fn scan_number(&mut self) -> Token {
        // Okay, first of all, numbers start with a decimal digit
        assert!(is_digit(self.cur.unwrap(), 10));

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

        // The integer part may contain no digits, like in "0x__"
        if digits == 0 {
            self.report.error(Span::new(self.start, self.prev_pos),
                "number contains no digits");
        }

        // According to what we have seen up to this point, it is integer
        let mut integer = true;

        // Though, a dot after an integer may mark a floating-point literal...
        if self.cur_is('.') {
            let c = self.peek().unwrap_or('\0');

            // ... if it is followed by another (decimal) integer
            if is_digit(c, 10) || c == '_' {
                self.read();
                self.scan_float_fractional_part();
                integer = false;
            } else {
                // Else it is just an integer followed by some dot. While dots can form identifiers
                // (like '...'), type suffixes are defined as word-identifiers, which dots aren't.
                // Thus we just go out with the suffixless integer we have already scanned over.
                let literal = self.intern_slice(self.start, self.prev_pos);
                return Token::Literal(Lit::Integer(literal), None);
            }
        }

        // An 'e' may start either a floating-point exponent, or (technically) a type suffix.
        // This is ambiguous, so we resolve it by greedily favoring the exponent treatment.
        if self.cur_is('e') || self.cur_is('E') {
            let c = self.peek().unwrap_or('\0');

            if is_digit(c, 10) || c == '_' {
                // An 'e' followed by a number is an exponent
                self.read();
                self.scan_float_exponent();
                integer = false;
            } else if c == '+' || c == '-' {
                // An 'e' followed by a sign which is followed by a number is an exponent.
                // If the sign is not followed by a number then we've seen just a suffix "e"
                // with '+' or '-' being a part of some mark-identifier that follows.
                let c = self.peekpeek().unwrap_or('\0');

                if is_digit(c, 10) || c == '_' {
                    self.read();
                    self.read();
                    self.scan_float_exponent();
                    integer = false;
                }
            } else {
                // Not an exponent, just some (invalid) type suffix starting with 'e'.
                // But we are in lexer and have no idea about is validity, so we go along.
            }
        }

        let literal = self.intern_slice(self.start, self.prev_pos);

        let suffix = self.scan_optional_type_suffix();

        // Some late check for floating-point base. We do not support binary literals for floats.
        if !integer && (base != 10) {
            self.report.error(Span::new(self.start, self.prev_pos),
                "only decimal base is supported for floating-point numbers");
        }

        return Token::Literal(if integer {
            Lit::Integer(literal)
        } else {
            Lit::Float(literal)
        }, suffix);
    }

    /// Scan over a sequence of digits.
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
                if !is_digit(c, base) {
                    if is_digit(c, allowed) {
                        self.report.error(Span::new(self.prev_pos, self.pos), match base {
                            2  => format!("invalid digit '{}', expected binary '0'..'1'", c),
                            8  => format!("invalid digit '{}', expected octal '0'..'7'", c),
                            10 => format!("invalid digit '{}', expected decimal '0'..'9'", c),
                            16 => format!("invalid digit '{}', expected hexadecimal '0'..'F'", c),
                            _  => panic!("unsupported base {}", base),
                        }.as_ref());
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

    /// Scan over a fractional part of a floating-point literal.
    fn scan_float_fractional_part(&mut self) {
        assert!(is_digit(self.cur.unwrap(), 10) || self.cur_is('_'));

        let fractional_start = self.prev_pos;
        let fractional_digits = self.scan_digits(10, 10);

        if fractional_digits == 0 {
            self.report.error(Span::new(fractional_start, self.prev_pos),
                "fractional part contains no digits");
        }
    }

    /// Scan over an exponent part of a floating-point literal.
    fn scan_float_exponent(&mut self) {
        assert!(is_digit(self.cur.unwrap(), 10) || self.cur_is('_'));

        let exponent_start = self.prev_pos;
        let exponent_digits = self.scan_digits(10, 10);

        if exponent_digits == 0 {
            self.report.error(Span::new(exponent_start, self.prev_pos),
                "exponent contains no digits");
        }
    }

    /// Scan over a single character literal.
    fn scan_character_literal(&mut self) -> Token {
        use self::CharacterSpecials::{SingleQuote, UnexpectedTerminator};

        // A character literal is a single quote...
        self.expect_and_skip("\'");

        let value = match self.scan_one_character_of_character() {
            // ...followed by one character...
            Ok(c) => {
                match self.scan_one_character_of_character() {
                    // ...and then by another single quote.
                    Err(SingleQuote) => {
                        self.read();
                        Some(c)
                    }
                    // If that's not a quote, pretend that we are scanning over a string, assuming
                    // that this is a one-line string mistakingly delimited by single quotes. But
                    // if it's not one-line then maybe this is not a character literal at all, the
                    // first quote character was lie, and we have scanned over something valuable.
                    // The same logic applies to all following uses of `UnexpectedTerminator`.
                    Ok(_) => {
                        let mut terminated = true;
                        loop {
                            // We are scanning characters as character literal characters in order
                            // to treat line endings as terminators, not as constituents.
                            match self.scan_one_character_of_character() {
                                // Skip over any constituents
                                Ok(_) => { }
                                // We have seen a closing quote on the same line, stop scanning
                                Err(SingleQuote) => {
                                    self.read();
                                    self.report.error(Span::new(self.start, self.prev_pos),
                                        "more than one character in a character constant");
                                    break;
                                }
                                // We did not see a closing quote on the same line, abort scanning
                                Err(UnexpectedTerminator) => {
                                    terminated = false;
                                    break;
                                }
                            }
                        }
                        if terminated {
                            Some(REPLACEMENT_CHARACTER)
                        } else {
                            None
                        }
                    }
                    Err(UnexpectedTerminator) => { None }
                }
            }
            // A literal single quote may be immediately followed by another literal single quote
            // in two cases: ''' (a correct character literal) and '' (incorrect empty character).
            Err(SingleQuote) => {
                self.read();
                if self.cur_is('\'') {
                    self.read();
                    Some('\'')
                } else {
                    self.report.error(Span::new(self.start, self.prev_pos),
                        "missing character in a character constant");
                    Some(REPLACEMENT_CHARACTER)
                }
            }
            Err(UnexpectedTerminator) => { None }
        };

        match value {
            Some(c) => {
                let suffix = self.scan_optional_type_suffix();

                return Token::Literal(Lit::Character(self.intern_string(c.to_string())), suffix);
            }
            None => {
                self.report.fatal(Span::new(self.start, self.prev_pos),
                    "unterminated character constant, expected a closing single quote (')");

                return Token::Unrecognized;
            }
        }
    }

    /// Scan over a string literal.
    fn scan_string(&mut self) -> Token {
        use self::StringSpecials::{DoubleQuote, SkippedEscapedLineEnding, UnexpectedTerminator};

        // Strings start with a double quote...
        self.expect_and_skip("\"");

        let mut value = String::new();

        loop {
            match self.scan_one_character_of_string() {
                // ...then it contains some characters...
                Ok(c) => {
                    value.push(c);
                }
                // ...or escaped line endings, which are ignored...
                Err(SkippedEscapedLineEnding) => { }
                // ...and finally the string ends with a closing double quote.
                Err(DoubleQuote) => {
                    self.read();
                    break;
                }
                // But things go wrong sometimes and the string may not be terminated
                Err(UnexpectedTerminator) => {
                    // For strings there is only one way to get here: end of the stream
                    self.report.fatal(Span::new(self.start, self.prev_pos),
                        "unterminated string, expected a closing double quote (\")");

                    return Token::Unrecognized;
                }
            }
        }

        let suffix = self.scan_optional_type_suffix();

        return Token::Literal(Lit::String(self.intern_string(value)), suffix);
    }

    /// Scan over an explicit symbol.
    fn scan_explicit_symbol(&mut self) -> Token {
        use self::SymbolSpecials::{Backquote, UnexpectedTerminator};

        // Symbols start with a backquote...
        self.expect_and_skip("`");

        let mut value = String::new();

        loop {
            match self.scan_one_character_of_symbol() {
                // ...then we have some characters...
                Ok(c) => {
                    value.push(c);
                }
                // ...and finally the symbol ends with a closing backquote.
                Err(Backquote) => {
                    self.read();
                    break;
                }
                // But things go wrong sometimes and the symbol may not be terminated
                Err(UnexpectedTerminator) => {
                    self.report.fatal(Span::new(self.start, self.prev_pos),
                        "unterminated symbol name, expected a closing backquote (`)");

                    return Token::Unrecognized;
                }
            }
        }

        return Token::ExplicitSymbol(self.intern_string(value));
    }

    /// Scan over a single character or escape sequence for a character literal.
    ///
    /// Returns an Ok character if it was scanned successfully, or a special indicator value
    /// if there was no character to scan. Note that there is a difference between 'successfully
    /// scanned over a character or an escape sequence' and 'scanned over a correct and valid
    /// character token'.
    fn scan_one_character_of_character(&mut self) -> Result<char, CharacterSpecials> {
        use self::CharacterSpecials::{SingleQuote, UnexpectedTerminator};

        match self.cur {
            // Backslash is a marker of escape sequences
            Some('\\') => {
                return self.scan_character_escape_sequence();
            }
            // Character literals cannot contain multiple characters in them, and cannot contain
            // explicit line endings (not even a single one). We tolerate and recover from multiple
            // characters on the same line as this may happen accidentally (e.g., denormalized
            // composite Unicode), but anything mulitline is an instant parsing failure. The users
            // must fix their code in the case as the scanner cannot and must not guess where their
            // intended string actually ends.
            Some('\n') => {
                return Err(UnexpectedTerminator);
            }
            Some('\r') if self.peek_is('\n') => {
                return Err(UnexpectedTerminator);
            }
            // Characters are correctly terminated by a single quote character. But they may also
            // contain it, as in ''' or '\u{27}'. Obviously, we need to discern between a literal
            // quote (which may be a terminator) and its Unicode escape form (which is never one).
            Some('\'') => {
                return Err(SingleQuote);
            }
            // Everything else is just a single character
            Some(c) => {
                // Drop a warning about a bare CR character. It is *not considered* a line ending,
                // but must be escaped in characters. These characters are often results of VCS
                // misconfiguration or other kind of blind automated tampering with source file
                // contents. None of the popular operating systems uses bare CRs as line endings.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "CR must be escaped in character constants: \\r");
                }
                self.read();
                return Ok(c);
            }
            // We expected at least one character or a closing quote
            None => {
                return Err(UnexpectedTerminator);
            }
        }
    }

    /// Scan over a single character or escape sequence for a string literal.
    ///
    /// Returns an Ok character if it was scanned successfully, or a special indicator value
    /// if there was no character to scan. Note that there is a difference between 'successfully
    /// scanned over a character or an escape sequence' and 'scanned over a correct and valid
    /// string token'.
    fn scan_one_character_of_string(&mut self) -> Result<char, StringSpecials> {
        use self::StringSpecials::{DoubleQuote, UnexpectedTerminator};

        match self.cur {
            // Backslash is a marker of escape sequences
            Some('\\') => {
                return self.scan_string_escape_sequence();
            }
            // String literals may contain multiple lines. The only special thing about them
            // is that Windows line endings are normalized into UNIX ones.
            Some('\n') => {
                self.read();
                return Ok('\n');
            }
            Some('\r') if self.peek_is('\n') => {
                self.read(); // TODO: this may cause issues if read() is taught to skip over
                self.read(); //       Windows line endings as a single character
                return Ok('\n');
            }
            // Strings are correctly terminated by a double quote character. But they may also
            // contain it, as in "\"" or "\u{27}". Obviously, we need to discern between a literal
            // quote (which may be a terminator) and its Unicode escape form (which is never one).
            Some('"') => {
                return Err(DoubleQuote);
            }
            // Everything else is just a single character
            Some(c) => {
                // Drop a warning about a bare CR character. It is *not considered* a line ending,
                // but must be escaped in characters. These characters are often results of VCS
                // misconfiguration or other kind of blind automated tampering with source file
                // contents. None of the popular operating systems uses bare CRs as line endings.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "bare CR is not allowed in strings, use \\r instead");
                }
                self.read();
                return Ok(c);
            }
            // We expected at least one character or a closing quote
            None => {
                return Err(UnexpectedTerminator);
            }
        }
    }

    /// Scan over a single character or escape sequence for an explicit symbol.
    ///
    /// Returns an Ok character if it was scanned successfully, or a special indicator value
    /// if there was no character to scan. Note that there is a difference between 'successfully
    /// scanned over a character or an escape sequence' and 'scanned over a correct and valid
    /// symbol token'.
    fn scan_one_character_of_symbol(&mut self) -> Result<char, SymbolSpecials> {
        use self::SymbolSpecials::{Backquote, UnexpectedTerminator};

        match self.cur {
            // Backslash is a marker of escape sequences
            Some('\\') => {
                return self.scan_symbol_escape_sequence();
            }
            // Symbols cannot contain explicit line endings (i.e., cannot span multiple lines).
            // Anything multiline is an instant parsing failure as the initial backquote may
            // have been erroneously placed and because of that we have scanned over something
            // valuable that was not intended to be a symbol at all. Or the closing backquote
            // has been forgotten and we have scanned over more than intended. The users must
            // fix their code in this case as the scanner cannot and must not guess where their
            // intended symbol actually ends.
            Some('\n') => {
                return Err(UnexpectedTerminator);
            }
            Some('\r') if self.peek_is('\n') => {
                return Err(UnexpectedTerminator);
            }
            // Symbols are correctly terminated by a backquote character. But they may also
            // contain it, as in `\`` or `\u{60}`. Obviously, we need to discern between a literal
            // quote (which may be a terminator) and its Unicode escape form (which is never one).
            Some('`') => {
                return Err(Backquote);
            }
            // Everything else is just a single character
            Some(c) => {
                // Drop a warning about a bare CR character. It is *not considered* a line ending,
                // but must be escaped in characters. These characters are often results of VCS
                // misconfiguration or other kind of blind automated tampering with source file
                // contents. None of the popular operating systems uses bare CRs as line endings.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "CR must be escaped in symbol names: \\r");
                }
                self.read();
                return Ok(c);
            }
            // We expected at least one character or a closing quote
            None => {
                return Err(UnexpectedTerminator);
            }
        }
    }

    /// Scan over a single character or escape sequence for an identifier.
    /// Returns an Ok character if it was scanned successfully, or a special indicator value
    /// if there was no character to scan. Note that there is a difference between 'successfully
    /// scanned over a character or an escape sequence' and 'scanned over a correct and valid
    /// identifier'.
    fn scan_one_character_of_identifier(&mut self) -> Result<char, IdentifierSpecials> {
        use self::IdentifierSpecials::{Terminator, Dot, Digit};

        match self.cur {
            // Backslash is a marker of escape sequences
            Some('\\') => {
                return self.scan_identifier_escape_sequence();
            }
            // Identifiers have a pretty impressive terminator list. Basically, it's everything
            // that is definitely not an ASCII identifier constituent and starts some other token,
            // including the whitespace and the end of character stream.
            Some('(') | Some(')') | Some('[') | Some(']') | Some('{') | Some('}') | Some(',') |
            Some(';') | Some(':') | Some('"') | Some(' ') | Some('\'') | Some('\n') | Some('\r') |
            Some('\t') | Some('#') | Some('`') | None => {
                return Err(Terminator);
            }
            // There are a couple of exceptions, though. Comments are delimited by characters from
            // mark identifier set. However, sequences "/*" and "//" are not allowed in them.
            // Non-mark identifiers form a boundary when followed by these characters
            Some('/') if (self.peek_is('/') || self.peek_is('*')) => {
                return Err(Terminator);
            }
            // Also, dots may or may not be constituents of mark identifiers. However, here
            // we do not know the kind of identifier is being scanned, so we defer processing
            // of this case to the caller.
            Some('.') => {
                return Err(Dot);
            }
            // The same this is with decimal digits which are continuations of word identifiers,
            // but they are terminators for all other identifier kinds as they start numbers.
            Some('0') | Some('1') | Some('2') | Some('3') | Some('4') |
            Some('5') | Some('6') | Some('7') | Some('8') | Some('9') => {
                return Err(Digit);
            }
            // Everything else is just a single character
            Some(c) => {
                self.read();
                return Ok(c);
            }
        }
    }

    /// Scan over an escape sequence allowed in character literals.
    ///
    /// Returns an Ok value denoted by the sequence (which is not guaranteed to be accurate),
    /// or a special indicator value.
    fn scan_character_escape_sequence(&mut self) -> Result<char, CharacterSpecials> {
        // All escape sequences start with a backslash
        self.expect_and_skip("\\");

        match self.cur {
            // \u... is a universal marker of a Unicode escape
            Some('u') => {
                return Ok(self.scan_escape_unicode(Some('\'')).unwrap_or(REPLACEMENT_CHARACTER));
            }

            // C-style escape sequences and ASCII byte escapes
            Some('0')  => { self.read(); return Ok('\0'); }
            Some('t')  => { self.read(); return Ok('\t'); }
            Some('n')  => { self.read(); return Ok('\n'); }
            Some('r')  => { self.read(); return Ok('\r'); }
            Some('"')  => { self.read(); return Ok('\"'); }
            Some('\\') => { self.read(); return Ok('\\'); }
            Some('x')  => { return Ok(self.scan_escape_byte()); }

            // A backslash denotes itself when it is followed by a terminator of a character
            // literal. The single quote will be scanned over by the caller, line endings and
            // the end of stream will also be handled by the caller. Here we just scan over
            // the backslash we are going to return.
            Some('\n') | Some('\'') | None => {
                return Ok('\\');
            }
            Some('\r') if self.peek_is('\n') => {
                return Ok('\\');
            }

            // Everything else is not expected to follow a backslash a means some invalid
            // escape sequence. Return that character as the value of the escape sequence.
            Some(c) => {
                // Report bare CRs just in case the user meant to follow the backslash with
                // a line ending, but has a crappy text editor. They will be included intact
                // into the character or the string being scanned.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "CR must be escaped in character constants: \\r");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "unknown escape sequence");
                self.read();
                return Ok(c);
            }
        }
    }

    /// Scan over an escape sequence allowed in string literals.
    ///
    /// Returns an Ok value denoted by the sequence (which is not guaranteed to be accurate),
    /// or a special indicator value.
    fn scan_string_escape_sequence(&mut self) -> Result<char, StringSpecials> {
        use self::StringSpecials::{SkippedEscapedLineEnding, UnexpectedTerminator};

        // All escape sequences start with a backslash
        self.expect_and_skip("\\");

        match self.cur {
            // \u... is a universal marker of a Unicode escape
            Some('u') => {
                return Ok(self.scan_escape_unicode(Some('"')).unwrap_or(REPLACEMENT_CHARACTER));
            }

            // C-style escape sequences and ASCII byte escapes
            Some('0')  => { self.read(); return Ok('\0'); }
            Some('t')  => { self.read(); return Ok('\t'); }
            Some('n')  => { self.read(); return Ok('\n'); }
            Some('r')  => { self.read(); return Ok('\r'); }
            Some('"')  => { self.read(); return Ok('\"'); }
            Some('\\') => { self.read(); return Ok('\\'); }
            Some('x')  => { return Ok(self.scan_escape_byte()); }

            // A backslash followed by a line ending is an escaped line ending. We scan over the
            // backslash, the line ending, and any additional whitespace following it, and then
            // go back to the caller.
            Some('\n') => {
                self.scan_whitespace();
                return Err(SkippedEscapedLineEnding);
            }
            Some('\r') if self.peek_is('\n') => {
                self.scan_whitespace();
                return Err(SkippedEscapedLineEnding);
            }

            // Everything else is not expected to follow a backslash a means some invalid
            // escape sequence. Return that character as the value of the escape sequence.
            Some(c) => {
                // Report bare CRs just in case the user meant to follow the backslash with
                // a line ending, but has a crappy text editor. They will be included intact
                // into the character or the string being scanned.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "CR must be escaped in strings: \\r");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "unknown escape sequence");
                self.read();
                return Ok(c);
            }

            // Ugh, an end of stream right after a backslash. We are scanning a string,
            // backslashes must be always escaped here (this is optional in characters).
            // Immediately notify the caller that a closing double quote will never arrive.
            None => {
                return Err(UnexpectedTerminator);
            }
        }
    }

    /// Scan over an escape sequence allowed in explicit symbols.
    ///
    /// Returns an Ok value denoted by the sequence (which is not guaranteed to be accurate),
    /// or a special indicator value.
    fn scan_symbol_escape_sequence(&mut self) -> Result<char, SymbolSpecials> {
        use self::SymbolSpecials::{UnexpectedTerminator};

        // All escape sequences start with a backslash
        self.expect_and_skip("\\");

        match self.cur {
            // \u... is a universal marker of a Unicode escape
            Some('u') => {
                return Ok(self.scan_escape_unicode(Some('`')).unwrap_or(REPLACEMENT_CHARACTER));
            }

            // C-style escape sequences and ASCII byte escapes
            Some('0')  => { self.read(); return Ok('\0'); }
            Some('t')  => { self.read(); return Ok('\t'); }
            Some('n')  => { self.read(); return Ok('\n'); }
            Some('r')  => { self.read(); return Ok('\r'); }
            Some('"')  => { self.read(); return Ok('\"'); }
            Some('\\') => { self.read(); return Ok('\\'); }
            Some('x')  => { return Ok(self.scan_escape_byte()); }

            // Special escape sequence for the backquote character in symbols
            Some('`')  => { self.read(); return Ok('`'); }

            // Ugh, an end of stream or line right after a backslash. We are scanning a symbol,
            // backslashes must be always escaped here. Immediately notify the caller that
            // a closing backquote will never arrive.
            Some('\n') | None => {
                return Err(UnexpectedTerminator);
            }
            Some('\r') if self.peek_is('\n') => {
                return Err(UnexpectedTerminator);
            }

            // Everything else is not expected to follow a backslash a means some invalid
            // escape sequence. Return that character as the value of the escape sequence.
            Some(c) => {
                // Report bare CRs just in case the user meant to follow the backslash with
                // a line ending, but has a crappy text editor. They will be included intact
                // into the symbol being scanned.
                if c == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "CR must be escaped in symbol names: \\r");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "unknown escape sequence");
                self.read();
                return Ok(c);
            }
        }
    }

    /// Scan over an escape sequence allowed in identifiers.
    ///
    /// Returns an Ok value denoted by the sequence (which is not guaranteed to be accurate),
    /// or a special indicator value.
    fn scan_identifier_escape_sequence(&mut self) -> Result<char, IdentifierSpecials> {
        use self::IdentifierSpecials::{IncorrectUnicodeEscape, AsciiUnicodeEscape};

        // All escape sequences start with a backslash
        self.expect_and_skip("\\");

        match self.cur {
            // \u... is a universal marker of a Unicode escape
            Some('u') => {
                return match self.scan_escape_unicode(None) {
                    // Do not allow ASCII characters to be written as Unicode escapes.
                    //
                    // Rationale:
                    //
                    //   1. Unicode escapes may be surprisingly abused in some contexts,
                    //      such as "♠.\u{2E}", "\u{2E}..", "+\u{31}2".
                    //
                    //   2. They are intended as a fallback for Unicode characters,
                    //      not as a generic ASCII encoding for programs.
                    //
                    //   3. Other ASCII-only tokens do not allow escapes.
                    Some(c) if c <= '\u{7F}' => Err(AsciiUnicodeEscape),
                    Some(c)                  => Ok(c),
                    None                     => Err(IncorrectUnicodeEscape)
                };
            }

            // Identifiers don't allow any escape sequences other than Unicode escapes.
            // Just return the backslash we have scanned over. It will be treated as invalid.
            _ => {
                return Ok('\\');
            }
        }
    }

    /// Scan over a single byte escape sequence. Returns its value.
    fn scan_escape_byte(&mut self) -> char {
        // Byte escapes start with \x, we have already seen the backslash
        self.expect_and_skip("x");

        let mut digits = 0;
        let mut value: u8 = 0;

        let escape_start = self.prev_pos - 2; // unwinding "\x"
        while !self.at_eof() {
            let c = self.cur.unwrap();
            if !is_digit(c, 16) {
                break;
            }
            // We don't care about overflows here as they can only be caused by
            // reading more that two non-zero digits which is already an error.
            value = value.wrapping_shl(4) | hex_value(c);
            digits += 1;
            self.read();
        }
        let digits_end = self.prev_pos;

        if digits != 2 {
            self.report.error(Span::new(escape_start, digits_end),
                "expected exactly two hexadecimal digits in a byte escape (e.g., \\x3A)");
            return REPLACEMENT_CHARACTER;
        }

        if value > 0x7F {
            self.report.error(Span::new(escape_start, digits_end),
                "byte escapes can only encode ASCII characters (\\x00..\\x7F)");
            return REPLACEMENT_CHARACTER;
        }

        return value as char;
    }

    /// Scan over a single Unicode escape sequence.
    ///
    /// Returns Some value of the escape sequence, or None if the sequence was legible
    /// but otherwise incorrect.
    fn scan_escape_unicode(&mut self, extra_delimiter: Option<char>) -> Option<char> {
        // Unicode escapes start with \u, we have already seen the backslash
        self.expect_and_skip("u");

        let escape_start = self.prev_pos - 2; // unwinding "\u"
        let brace_start = self.prev_pos;

        // Unicode scalar value should be braced, so it must start with a '{'
        let missing_open = match self.cur {
            Some('{') => {
                self.read();
                false
            }
            _ => { true }
        };

        let mut empty_braces = true;
        let mut invalid_hex = false;
        let mut missing_close = false;
        let mut value: u32 = 0;
        let mut unicode_overflow = false;

        loop {
            match self.cur {
                // If a Unicode scalar is braced then it ends with a '}'
                Some('}') => {
                    self.read();
                    break;
                }
                // Encountered a clear terminator of a Unicode escape, but have not seen '}'.
                // Terminators include a backslash (likely to start the next escape sequence),
                // the end of stream (obvioulsy), a line ending (likely to mean a forgotten brace),
                // and a caller-provided additional character (if any, this will be a single or
                // a double quote character expected to terminate the character or string literal).
                Some('\\') | None => {
                    missing_close = true;
                    break;
                }
                Some('\n') => {
                    missing_close = true;
                    break;
                }
                Some('\r') if self.peek_is('\n') => {
                    missing_close = true;
                    break;
                }
                Some(c) if Some(c) == extra_delimiter => {
                    missing_close = true;
                    break;
                }
                // Otherwise, it may be a constituent hexadecimal digit, an invalid character,
                // or another terminator, depending on whether we have seen an opening brace.
                Some(c) => {
                    let valid_digit = is_digit(c, 16);

                    // Braced syntax of Unicode escapes allows adding support for named Unicode
                    // characters in a backwards-compatible way. However, right now we do not have
                    // them. So we just tweak error reporting a bit to be more reasonable.
                    //
                    // If we are scanning a properly braced escape we just skip everything that
                    // does not look like a hex digit. Of course, we take notes of it and report
                    // invalid characters. If we look at an (erroneous) old-skool "\uF0F0" escape,
                    // we just stop at the first non-hex-digit assuming an end of the escape code.

                    if !valid_digit {
                        if missing_open {
                            missing_close = true;
                            break;
                        }
                        invalid_hex = true;
                    }

                    empty_braces = false;

                    // Add hex digits to the codepoint value if possible. Take care to notice when
                    // the value overflows the Unicode range and avoid further arithmetic overflow.

                    if valid_digit && !invalid_hex && !unicode_overflow {
                        value = (value << 4) | (hex_value(c) as u32);
                        if value > 0x10FFFF {
                            unicode_overflow = true;
                        }
                    }
                }
            }
            self.read();
        }

        let brace_end = self.prev_pos;

        let surrogate_code_point = (0xD800 <= value) && (value <= 0xDFFF);

        // Keep our mouth shut about missing/asymmetric braces if there is nothing in them anyway
        if empty_braces {
            self.report.error(Span::new(brace_start, brace_end),
                "invalid Unicode character escape: missing character value");

            return None;
        }

        if missing_open || missing_close {
            let invalid_unicode = invalid_hex || unicode_overflow || surrogate_code_point;
            let model_value = if invalid_unicode { 0x2468 } else { value };

            self.report.error(
                match (missing_open, missing_close) {
                    (true, true) => Span::new(brace_start, brace_end),
                    (true, false) => Span::new(brace_start, brace_start),
                    (false, true) => Span::new(brace_end, brace_end),
                    (false, false) => unreachable!(),
                },
                format!("Unicode scalar value must be surrounded with braces: \
                         \\u{{{:X}}}", model_value).as_ref());
        }

        if invalid_hex {
            self.report.error(Span::new(escape_start, brace_end),
                "invalid Unicode character escape: expected only hexadecimal digits");

            return None;
        }

        if unicode_overflow {
            self.report.error(Span::new(escape_start, brace_end),
                "invalid Unicode character escape: character value cannot be larger \
                 than \\u{10FFFF}");

            return None;
        }

        if surrogate_code_point {
            self.report.error(Span::new(escape_start, brace_end),
                "invalid Unicode character escape: character values in range from \\u{D800} \
                 to \\u{DFFF} inclusive (surrogate code points) are not allowed");

            return None;
        }

        // At this point we have ensured that `value` *is* a valid Unicode scalar value
        assert!((value <= 0x10FFFF) && !((0xD800 <= value) && (value <= 0xDFFF)));

        // TODO: Replace this with std::char::from_u32_unchecked() when it is stabilized
        return Some(char::from_u32(value).unwrap());
    }

    /// Scan over raw string leading sequence `r#...#"`.
    ///
    /// Returns Some number of hashes scanned over in case of success, or None if the string
    /// did not look like a raw string leading sequence.
    ///
    /// In case of success the scanner state is set to the opening quote. If the character string
    /// does not look like a raw string, the scanner is stopped right after the `r` character.
    fn scan_raw_string_leaders(&mut self) -> Option<u32> {
        // Raw strings start with 'r'
        self.expect_and_skip("r");

        // Yes. Unfortunately, we need infinite lookahead to handle this case.
        // Well, whatever, raw strings have a context-sensitive grammar.

        let mut hash_count = 0;
        for cur in self.buf[self.prev_pos..].chars() {
            match cur {
                '#' => { hash_count += 1; }
                '"' => {
                    // Keep this an equivalent of `for 0..hash_count { self.read(); }`
                    self.prev_pos += hash_count as usize;
                    self.pos += hash_count as usize;
                    self.cur = Some('"');

                    return Some(hash_count);
                }
                _  => { break; }
            }
        }

        return None;
    }

    /// Scan over a raw string delimited by `hash_count` hashes.
    fn scan_raw_string(&mut self, hash_count: u32) -> Token {
        // Raw string content starts with an double quote
        self.expect_and_skip("\"");

        let mut value = String::new();

        loop {
            match self.cur {
                Some('"') => {
                    match self.scan_raw_string_trailers(hash_count) {
                        Some(chunk) => {
                            value.push_str(chunk);
                        }
                        None => {
                            break;
                        }
                    }
                }
                Some(c) => {
                    if c == '\r' {
                        if self.peek() != Some('\n') {
                            self.report.error(Span::new(self.prev_pos, self.pos),
                                "bare CR is not allowed in raw strings, use \\r instead");
                            value.push('\r');
                        }
                    } else {
                        value.push(c);
                    }
                    self.read();
                }
                None => {
                    self.report.fatal(Span::new(self.start, self.prev_pos),
                        match hash_count {
                            0 => format!("unterminated raw string, expected a double quote (\")"),
                            1 => format!("unterminated raw string, expected a double quote \
                                        followed by a hash (\"#)"),
                            _ => format!("unterminated raw string, expected a double quote (\") \
                                          followed by {} hashes (#)", hash_count),
                    }.as_ref());

                    return Token::Unrecognized;
                }
            }
        }

        let suffix = self.scan_optional_type_suffix();

        return Token::Literal(Lit::RawString(self.intern_string(value)), suffix);
    }

    /// Scan over raw string trailing sequence `"#...#`.
    ///
    /// Scanner stops either at the first non-`#` character, or at the end of file, or when
    /// `hash_count` hashes have been scanned over, whichever comes first.
    ///
    /// Returns None when a correct trailing sequence was scanned, or Some slice of text if there
    /// were not enough hashes after the quote and the raw string content possibly goes on. The
    /// slice contains the part of buffer that has been scanned over.
    fn scan_raw_string_trailers(&mut self, hash_count: u32) -> Option<&str> {
        let chunk_start = self.prev_pos;

        // Raw string content ends with an double quote
        self.expect_and_skip("\"");

        let mut seen = 0;

        while seen < hash_count {
            if self.cur_is('#') {
                seen += 1;
                self.read();
            } else {
                let chunk_end = self.prev_pos;

                return Some(&self.buf[chunk_start..chunk_end]);
            }
        }

        return None;
    }

    /// Scan over an identifier or maybe an implicit symbol.
    fn scan_identifier_or_symbol(&mut self) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Look at the first character to decide what kind of identifier we're up to
        match self.scan_one_character_of_identifier() {
            Ok(c) => {
                let category = sash_identifiers::category_of(c);

                // If it's a valid starter then dispatch to kind-specific loops
                if category.is(WORD_START) {
                    return self.scan_identifier_word_or_symbol(c);
                }
                if category.is(MARK_START) {
                    return self.scan_identifier_mark(c);
                }
                if category.is(QUOTE_START) {
                    return self.scan_identifier_quote(c);
                }

                // Otherwise, skip over this incomprehensible character sequence until we see
                // something meaninful. We *can* go here as scan_identifier() is called by the
                // catch-all branch of the next() method.
                return self.scan_unrecognized();
            }
            // Ignore invalid Unicode escapes as well
            Err(IncorrectUnicodeEscape) | Err(AsciiUnicodeEscape) => {
                return self.scan_unrecognized();
            }
            // In this context, a dot must be followed by another dot, meaning a mark identifier.
            // Token::Dot should have been handled by next() before.
            Err(Dot) => {
                assert!(self.peek_is('.'));
                return self.scan_identifier_mark('.');
            }
            // next() should have also handled these cases, so we will never get here.
            Err(Terminator) | Err(Digit) => { unreachable!(); }
        }
    }

    /// Scan over a sequence of unrecognized characters.
    fn scan_unrecognized(&mut self) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Scan over the characters until we see either a starter character for an identifier
        // or some other token. Silently skip over everything else
        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    if category.is(WORD_START | MARK_START | QUOTE_START) {
                        self.unread(c, old_prev_pos);
                        break;
                    }
                }
                Err(Dot) | Err(Terminator) | Err(Digit) => {
                    break;
                }
                Err(IncorrectUnicodeEscape) | Err(AsciiUnicodeEscape) => { }
            }
        }

        self.report.error(Span::new(self.start, self.prev_pos),
            "incomprehensible character sequence");

        return Token::Unrecognized;
    }

    /// Scan over a word identifier which starts with `initial` character.
    fn scan_identifier_word(&mut self, initial: char) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, WORD_CONTINUE, MARK_START, QUOTE_START};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Word identifiers must start with a proper starter
        assert!(sash_identifiers::category_of(initial).is(WORD_START));

        let mut value = String::new();
        value.push(initial);

        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                // Well, okay, another character has been correctly scanned over
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Just go on scanning thw word if this a valid continuation
                    if category.is(WORD_CONTINUE) {
                        value.push(c);
                        continue;
                    }

                    // However, if we have scanned over a starter of another identifier kind,
                    // put the character back into the buffer and stop scanning
                    if category.is(MARK_START | QUOTE_START) {
                        self.unread(c, old_prev_pos);
                        break;
                    }

                    // If this does not seem to be a valid continuation character, just report it,
                    // greedily eat it, and go on scanning, pretending that this was an accident.
                    value.push(c);
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        format!("this character not allowed in word identifiers: \
                                 '{}' (U+{:04X})", c, c as u32).as_ref());
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "escaped ASCII is not allowed in identifiers");
                }
                // Decimal digits are valid contiuations of word identifiers
                Err(Digit) => {
                    let c = self.cur.unwrap();
                    assert!(sash_identifiers::category_of(c).is(WORD_CONTINUE));
                    value.push(c);
                    self.read();
                    continue;
                }
                // A clean termiantor of an identifier has been seen.
                // This includes dots for words.
                Err(Dot) | Err(Terminator) => {
                    break;
                }
            }
        }

        return Token::Identifier(self.intern_string(value));
    }

    /// Scan over a standalone word identifier or maybe an implicit symbol which starts
    /// with `initial` character.
    fn scan_identifier_word_or_symbol(&mut self, initial: char) -> Token {
        let initial_token = self.scan_identifier_word(initial);

        // Word identifier followed by a single colon forms an implicit symbol token.
        if (self.cur_is(':')) && (self.peek() != Some(':')) {
            self.read();
            return match initial_token {
                Token::Identifier(atom) => Token::ImplicitSymbol(atom),
                _ => unreachable!()
            }
        }

        return initial_token;
    }

    /// Scan over a mark identifier which starts with `initial` character.
    fn scan_identifier_mark(&mut self, initial: char) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, MARK_CONTINUE, QUOTE_START};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Mark identifiers must start with a proper starter
        assert!(sash_identifiers::category_of(initial).is(MARK_START));

        let mut value = String::new();

        // The initial dot is not scanned over by scan_identifier_or_symbol() in order to allow
        // the loop below to make use of scan_one_character_of_identifier(). Do not add the dot
        // into the representation string right now, it will be correctly added afterwards.
        if initial != '.' {
            value.push(initial);
        }

        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                // Well, okay, another character has been correctly scanned over
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Just go on scanning thw word if this a valid continuation
                    if category.is(MARK_CONTINUE) {
                        value.push(c);
                        continue;
                    }

                    // However, if we have scanned over a starter of another identifier kind,
                    // put the character back into the buffer and stop scanning
                    if category.is(WORD_START | QUOTE_START) {
                        self.unread(c, old_prev_pos);
                        break;
                    }

                    // If this does not seem to be a valid continuation character, just report it,
                    // greedily eat it, and go on scanning, pretending that this was an accident.
                    value.push(c);
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        format!("this character not allowed in mark identifiers: \
                                 '{}' (U+{:04X})", c, c as u32).as_ref());
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "escaped ASCII is not allowed in identifiers");
                }
                // We have seen a literal dot. It is allowed in marks as long as it is followed by
                // at least one more literal dot. If that is the case, scan over all these dots.
                // Otherwise stop scanning the identifier without consuming this to-be-Token::Dot.
                Err(Dot) => {
                    if self.peek_is('.') {
                        while self.cur_is('.') {
                            value.push('.');
                            self.read();
                        }
                    } else {
                        break;
                    }
                }
                // A clean termiantor of an identifier has been seen.
                // This includes decimal digits for mark identifiers.
                Err(Terminator) | Err(Digit) => {
                    break;
                }
            }
        }

        return Token::Identifier(self.intern_string(value));
    }

    /// Scan over a quote identifier which starts with `initial` character.
    fn scan_identifier_quote(&mut self, initial: char) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START, QUOTE_CONTINUE};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Quote identifiers must start with a proper starter
        assert!(sash_identifiers::category_of(initial).is(QUOTE_START));

        let mut value = String::new();
        value.push(initial);

        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                // Well, okay, another character has been correctly scanned over
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Quote identifiers are one-character tokens. If we have scanned over
                    // a starter of any identifier kind, put the character back into the buffer
                    // and stop scanning.
                    if category.is(WORD_START | MARK_START | QUOTE_START) {
                        self.unread(c, old_prev_pos);
                        break;
                    }

                    // Otherwise, report an an error, consume the character, and go on scanning,
                    // pretending that this was an accident. We use a slightly different message
                    // for combining modifiers which are allowed in all other identifier kinds.
                    if category.is(QUOTE_CONTINUE) {
                        self.report.error(Span::new(old_prev_pos, self.prev_pos),
                            format!("combining modifiers are not allowed in quote identifiers: \
                                 ' {}' (U+{:04X})", c, c as u32).as_ref());
                    } else {
                        self.report.error(Span::new(old_prev_pos, self.prev_pos),
                            format!("this character not allowed in quote identifiers: \
                                 '{}' (U+{:04X})", c, c as u32).as_ref());
                    }
                    value.push(c);
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    value.push(REPLACEMENT_CHARACTER);
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "escaped ASCII is not allowed in identifiers");
                }
                // A clean termiantor of an identifier has been seen.
                // This includes decimal digits and dots for quote identifiers.
                Err(Dot) | Err(Terminator) | Err(Digit) => {
                    break;
                }
            }
        }

        return Token::Identifier(self.intern_string(value));
    }

    /// Maybe scan over an optional type suffix of literal tokens.
    fn scan_optional_type_suffix(&mut self) -> Option<Atom> {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START,
            WORD_CONTINUE, MARK_CONTINUE, QUOTE_CONTINUE};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        let old_prev_pos = self.prev_pos;
        match self.scan_one_character_of_identifier() {
            // Special case for raw string literals immediately following some
            // other literal. Their 'r' should not be considered a type suffix.
            Ok('r') if (self.cur_is('"')) || (self.cur_is('#')) => {
                self.unread('r', old_prev_pos);
            }
            // A character has been correctly scanned over. Scan over the type suffix if it looks
            // like a word, or else put the character back at where we took it and simply go out.
            Ok(c) => {
                let category = sash_identifiers::category_of(c);

                if category.is(WORD_START) {
                    return match self.scan_identifier_word(c) {
                        Token::Identifier(atom) => Some(atom),
                        _ => unreachable!(),
                    };
                }

                self.unread(c, old_prev_pos);
            }
            // Some incorrect escape sequence has been scanned over. This is certainly not going
            // to be a word, so we should put the character back. But we do not know the specific
            // code point when we scan over an invalid Unicode escape or an ASCII Unicode escape.
            // Yet we must unread() something invalid in identifiers in order to have the next
            // token to be Token::Unrecognized. We use an arbitrary contstant U+0000 for this.
            Err(IncorrectUnicodeEscape) | Err(AsciiUnicodeEscape) => {
                const INVALID_IDENTIFIER_CHARACTER: char = '\u{0}';

                assert!(sash_identifiers::category_of(INVALID_IDENTIFIER_CHARACTER).is(
                    WORD_START | MARK_START | QUOTE_START |
                    WORD_CONTINUE | MARK_CONTINUE | QUOTE_CONTINUE
                ) == false);

                self.unread(INVALID_IDENTIFIER_CHARACTER, old_prev_pos);
            }
            // A terminator of a word identifer is ahead (it has not been scanned over yet).
            // Just go out, there is nothing interesting for us here.
            Err(Dot) | Err(Terminator) | Err(Digit) => { }
        }

        return None;
    }
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Internal utility definitions
//

/// Unicode replacemente character.
///
/// It is currently used as a placeholder for invalid Unicode escape sequences.
const REPLACEMENT_CHARACTER: char = '\u{FFFD}';

/// Indicator values used in scanning character literals. These are returned by
/// `StringScanner::scan_one_character_of_character()` when the next character
/// is not a regular character of a literal.
enum CharacterSpecials {
    /// Literal single quote encountered. It has not been scanned over yet.
    SingleQuote,

    /// Unexpected terminator (a line ending or the end of stream) encountered.
    /// The line ending has not been scanned over yet.
    UnexpectedTerminator,
}

/// Indicator values used in scanning string literals. These are returned by
/// `StringScanner::scan_one_character_of_string()` when the next character
/// is not a regular character of a literal.
enum StringSpecials {
    /// Literal double quote encountered. It has not been scanned over yet.
    DoubleQuote,

    /// A backslash-escaped line ending has been skipped over, yielding no
    /// characters for the string.
    SkippedEscapedLineEnding,

    /// Unexpected terminator (the end of stream) encountered.
    UnexpectedTerminator,
}

/// Indicator values used in scanning explicit symbols. These are returned by
/// `StringScanner::scan_one_character_of_symbol()` when the next character
/// is not a regular character of a symbol.
enum SymbolSpecials {
    /// Literal backquote encountered. It has not been scanned over yet.
    Backquote,

    /// Unexpected terminator (a line ending or the end of stream) encountered.
    /// The line ending has not been scanned over yet.
    UnexpectedTerminator,
}

/// Indicator values used in scanning identifiers. These are returned by
/// `StringScanner::scan_one_character_of_identifier()` when the next character
/// is not a regular character of an identifier.
enum IdentifierSpecials {
    /// Literal dot encountered. It has not been scanned over yet.
    Dot,

    /// Literal decimal digit encountered. It has not been scanned over yet.
    Digit,

    /// Definite identifier terminator encountered (such as line ending, the
    /// end of stream, a comment starting sequence (`//` or `/*`), or some
    /// ASCII character that is not used in identifiers, like `[` or ':').
    /// The terminator character has not been scanned over yet.
    Terminator,

    /// Scanned over an invalid Unicode escape which did not produce
    /// a reliable character.
    IncorrectUnicodeEscape,

    /// Scanned over a Unicode escape representing an ASCII character.
    AsciiUnicodeEscape,
}

/// Checks whether `c` is a valid digit of base `base`.
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

/// Converts an ASCII hex digit character to its numeric value.
fn hex_value(c: char) -> u8 {
    assert!(is_digit(c, 16));

    const H: &'static [u8; 128] = &[
        0, 0, 0, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        0, 0, 0, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,
        0,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        0,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
    ];

    return H[c as usize];
}

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Tests
//

#[cfg(test)]
mod tests {
    use super::*;
    use tokens::{Token, Delimiter, Lit};
    use diagnostics;
    use diagnostics::{Span, SpanReporter, Severity};
    use intern_pool::{Atom, InternPool};

    macro_rules! check {
        { $( ( $($spec:tt)* ) ),* ; $( $severity:path : $( ($from:expr, $to:expr) ),+ ; )* } => {{
            let pool = InternPool::new();
            let slices = &[
                $( slice!(pool, $($spec)*) , )*
            ];
            let diagnostics = &[
                $( $( ($severity, Span::new($from, $to)), )+ )*
            ];
            check(slices, diagnostics, pool);
        }}
    }

    macro_rules! slice {
        { $pool:expr, $str:expr => $tok:ident } => {
            ScannerTestSlice($str, Token::$tok)
        };
        { $pool:expr, $str:expr => OpenDelim($delim:ident) } => {
            ScannerTestSlice($str, Token::OpenDelim(Delimiter::$delim))
        };
        { $pool:expr, $str:expr => CloseDelim($delim:ident) } => {
            ScannerTestSlice($str, Token::CloseDelim(Delimiter::$delim))
        };
        { $pool:expr, $str:expr => Literal($lit:ident, $val:expr) } => {
            ScannerTestSlice($str, Token::Literal(Lit::$lit($pool.intern($val)), None))
        };
        { $pool:expr, $str:expr => Literal($lit:ident, $val:expr, $suffix:expr) } => {
            ScannerTestSlice($str, Token::Literal(Lit::$lit($pool.intern($val)),
                                                  Some($pool.intern($suffix))))
        };
        { $pool:expr, $str:expr => $tok:ident($val:expr) } => {
            ScannerTestSlice($str, Token::$tok($pool.intern($val)))
        };
    }

    #[test]
    fn empty_string() {
        check! { ; }
    }

    #[test]
    fn whitespace() {
        check! {
            ("   \t\t\r\n  \t \t\n"     => Whitespace);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Line comments

    #[test]
    fn line_comment_lf() {
        check! {
            ("// example line comment"  => Comment),
            ("\n       \t"              => Whitespace);
        }
    }

    #[test]
    fn line_comment_crlf() {
        check! {
            ("// example line comment"  => Comment),
            ("\r\n       \t"            => Whitespace);
        }
    }

    #[test]
    fn line_comment_cr() {
        check! {
            ("// example line comment\r       \t" => Comment);

        Severity::Error:
            (23, 24);
        }
    }

    #[test]
    fn line_comment_consecutive_lf() {
        check! {
            ("// line 1" => Comment),
            ("\n"        => Whitespace),
            ("// line 2" => Comment),
            ("\n     "   => Whitespace);
        }
    }

    #[test]
    fn line_comment_consecutive_crlf() {
        check! {
            ("// line 1" => Comment),
            ("\r\n"      => Whitespace),
            ("// line 2" => Comment),
            ("\r\n     " => Whitespace);
        }
    }

    #[test]
    fn line_comment_consecutive_cr() {
        check! {
            ("// line 1\r// line 2\r     " => Comment);

        Severity::Error:
            (9, 10), (19, 20);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Block comments

    #[test]
    fn block_comment_simple() {
        check! {
            ("/* example */" => Comment);
        }
    }

    #[test]
    fn block_comment_multiline() {
        check! {
            ("/* example\non the next line */" => Comment);
        }
    }

    #[test]
    fn block_comment_nested() {
        check! {
            ("/* /* nested */ example /**/*/" => Comment);
        }
    }

    #[test]
    fn block_comment_consecutive() {
        check! {
            ("/*1*/" => Comment),
            ("\n"    => Whitespace),
            ("/*2*/" => Comment);
        }
    }

    #[test]
    fn block_comment_unterminated_1() {
        check! {
            ("/* forgot" => Unrecognized);

        Severity::Fatal:
            (0, 9);
        }
    }

    #[test]
    fn block_comment_unterminated_2() {
        check! {
            ("/*/" => Unrecognized);

        Severity::Fatal:
            (0, 3);
        }
    }

    #[test]
    fn block_comment_unterminated_nested() {
        check! {
            ("/*/*nested*/" => Unrecognized);

        Severity::Fatal:
            (0, 12);
        }
    }

    #[test]
    fn block_comment_line_comment_allows_unterminated_blocks() {
        check! {
            ("// /* doesn't matter" => Comment);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Doc comments

    #[test]
    fn doc_comment_line() {
        check! {
            ("/// Example"                                      => DocComment("/// Example")),
            ("\n"                                               => Whitespace),
            ("/// Other line"                                   => DocComment("/// Other line")),
            ("\r\n"                                             => Whitespace),
            ("/// More"                                         => DocComment("/// More")),
            ("\n\n"                                             => Whitespace),
            ("//! Inner comments"                               => DocComment("//! Inner comments")),
            ("\n"                                               => Whitespace),
            ("//! Windows lines"                                => DocComment("//! Windows lines")),
            ("\r\n\r\n"                                         => Whitespace),
            ("/// Mixed"                                        => DocComment("/// Mixed")),
            ("\n"                                               => Whitespace),
            ("//! Mixed"                                        => DocComment("//! Mixed")),
            ("\r\n"                                             => Whitespace);
        }
    }

    #[test]
    fn doc_comment_block() {
        check! {
            ("/** Example */"                                   => DocComment("/** Example */")),
            ("\n"                                               => Whitespace),
            ("/** Multiple\n    lines\r\n    are allowed */"    => DocComment("/** Multiple\n    lines\r\n    are allowed */")),
            ("\n"                                               => Whitespace),
            ("/*! Some more\n    inner\r\n comments !*/"        => DocComment("/*! Some more\n    inner\r\n comments !*/")),
            ("\r\n"                                             => Whitespace),
            ("/*! and /*! they /** can */ be ****/ nested */"   => DocComment("/*! and /*! they /** can */ be ****/ nested */")),
            ("/** in /*!! any */ way /* you */ like */"         => DocComment("/** in /*!! any */ way /* you */ like */"));
        }
    }

    #[test]
    fn doc_comment_intertype_nesting() {
        check! {
            ("/// This /* is fine */"                           => DocComment("/// This /* is fine */")),
            ("\n"                                               => Whitespace),
            ("//! This /*! is too"                              => DocComment("//! This /*! is too")),
            ("\r\n\n"                                           => Whitespace),
            ("/** Also // fine */"                              => DocComment("/** Also // fine */")),
            ("\n"                                               => Whitespace),
            ("/*! Fine as well // */"                           => DocComment("/*! Fine as well // */")),
            ("\r\n"                                             => Whitespace),
            ("// /// These are also"                            => Comment),
            ("\n"                                               => Whitespace),
            ("/* /** // fine */ */"                             => Comment);
        }
    }

    #[test]
    fn doc_comment_block_unterminated() {
        check! { ("/** forgot " => Unrecognized); Severity::Fatal: (0, 11); }
        check! { ("/*! as well" => Unrecognized); Severity::Fatal: (0, 11); }
        check! { ("/** /*nest"  => Unrecognized); Severity::Fatal: (0, 10); }
        check! { ("/*!/*!*/"    => Unrecognized); Severity::Fatal: (0,  8); }
    }

    #[test]
    fn doc_comment_bare_crs() {
        check! {
            ("/// bare crs\r///are errors"                      => DocComment("/// bare crs\r///are errors")),
            ("\n"                                               => Whitespace),
            ("//! in all\r\r\rkinds of doc-comments"            => DocComment("//! in all\r\r\rkinds of doc-comments")),
            ("\n\n"                                             => Whitespace),
            ("/** and I mean \r all */"                         => DocComment("/** and I mean \r all */")),
            ("\r\n"                                             => Whitespace),
            ("/*! like /* \r this */ */"                        => DocComment("/*! like /* \r this */ */"));

        Severity::Error:
            (12, 13), (37, 38), (38, 39), (39, 40), (78, 79), (100, 101);
        }
    }

    #[test]
    fn doc_comment_non_docs() {
        check! {
            ("/////////////////////////////////"                => Comment),
            ("\n"                                               => Whitespace),
            ("// These are not doc comments"                    => Comment),
            ("\n"                                               => Whitespace),
            ("/////////////////////////////////"                => Comment),
            ("\n\n"                                             => Whitespace),
            ("/***\r\n * These are not as well\n ***/"          => Comment),
            ("\n"                                               => Whitespace),
            ("//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!"                 => DocComment("//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!")),
            ("\n"                                               => Whitespace),
            ("//! Though this is one"                           => DocComment("//! Though this is one")),
            ("\n"                                               => Whitespace),
            ("//!/////////////////////////////"                 => DocComment("//!/////////////////////////////")),
            ("\n \n "                                           => Whitespace),
            ("/////////////////////////////////"                => Comment),
            ("\n"                                               => Whitespace),
            ("/// It's a bit tricky..."                         => DocComment("/// It's a bit tricky...")),
            ("\n"                                               => Whitespace),
            ("/////////////////////////////////"                => Comment),
            ("\n\r\n"                                           => Whitespace),
            ("/// As well as this one, and this:"               => DocComment("/// As well as this one, and this:")),
            ("\n"                                               => Whitespace),
            ("///"                                              => DocComment("///")),
            ("\n\n"                                             => Whitespace),
            ("/*!!! A doc-comment */"                           => DocComment("/*!!! A doc-comment */")),
            ("\r\t\n"                                           => Whitespace),
            ("/*!** A doc-comment as well **!*/"                => DocComment("/*!** A doc-comment as well **!*/")),
            ("\n"                                               => Whitespace),
            ("// This is not a doc comment:"                    => Comment),
            ("\n"                                               => Whitespace),
            ("/**/"                                             => Comment),
            ("// But this one is:"                              => Comment),
            ("\r\n"                                             => Whitespace),
            ("/*!*/"                                            => DocComment("/*!*/")),
            ("// And this one isn't:"                           => Comment),
            ("\n"                                               => Whitespace),
            ("/***/"                                            => Comment);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Brackets and other fixed tokens

    #[test]
    fn brackets() {
        check! {
            ("("     => OpenDelim(Paren)),
            ("]"     => CloseDelim(Bracket)),
            ("\n\n"  => Whitespace),
            ("}"     => CloseDelim(Brace)),
            ("}"     => CloseDelim(Brace)),
            (" "     => Whitespace),
            ("["     => OpenDelim(Bracket)),
            ("["     => OpenDelim(Bracket)),
            ("\t"    => Whitespace),
            ("("     => OpenDelim(Paren)),
            ("{"     => OpenDelim(Brace)),
            ("\r\n"  => Whitespace),
            (")"     => CloseDelim(Paren)),
            (")"     => CloseDelim(Paren));
        }
    }

    #[test]
    fn punctuation() {
        check! {
            (","    => Comma),
            ("."    => Dot),
            ("::"   => Dualcolon),
            ("."    => Dot),
            (":"    => Colon),
            (" "    => Whitespace),
            (":"    => Colon),
            ("."    => Dot),
            (";"    => Semicolon),
            ("("    => OpenDelim(Paren)),
            (";"    => Semicolon),
            (";"    => Semicolon),
            (","    => Comma),
            (","    => Comma),
            ("#"    => Hash),
            ("#"    => Hash);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Integers

    #[test]
    fn integer_basic_decimal() {
        check! {
            ("0"                        => Literal(Integer, "0")),
            (","                        => Comma),
            ("1"                        => Literal(Integer, "1")),
            (","                        => Comma),
            ("00000"                    => Literal(Integer, "00000")),
            (","                        => Comma),
            ("00001"                    => Literal(Integer, "00001")),
            ("."                        => Dot),
            (" "                        => Whitespace),
            ("42"                       => Literal(Integer, "42")),
            (" "                        => Whitespace),
            ("913784782364235463746343" => Literal(Integer, "913784782364235463746343")),
            ("\n"                       => Whitespace),
            ("("                        => OpenDelim(Paren)),
            ("12345"                    => Literal(Integer, "12345")),
            (")"                        => CloseDelim(Paren)),
            ("67890"                    => Literal(Integer, "67890"));
        }
    }

    #[test]
    fn integer_basic_nondecimal() {
        check! {
            ("0b0110101010"             => Literal(Integer, "0b0110101010")),
            (","                        => Comma),
            ("0o755"                    => Literal(Integer, "0o755")),
            (","                        => Comma),
            ("0o32"                     => Literal(Integer, "0o32")),
            (","                        => Comma),
            ("0o0"                      => Literal(Integer, "0o0")),
            (","                        => Comma),
            ("0xDBE"                    => Literal(Integer, "0xDBE")),
            (","                        => Comma),
            ("0x12345"                  => Literal(Integer, "0x12345")),
            (","                        => Comma),
            ("0xDeadBeef"               => Literal(Integer, "0xDeadBeef")),
            (","                        => Comma),
            ("0xAAAAAAAAAAAAA"          => Literal(Integer, "0xAAAAAAAAAAAAA"));
        }
    }

    #[test]
    fn integer_separators() {
        check! {
            ("0___"                     => Literal(Integer, "0___")),
            (" "                        => Whitespace),
            ("10_000"                   => Literal(Integer, "10_000")),
            (" "                        => Whitespace),
            ("1_2_3_4_5"                => Literal(Integer, "1_2_3_4_5")),
            (" "                        => Whitespace),
            ("0x__5__"                  => Literal(Integer, "0x__5__")),
            (" "                        => Whitespace),
            ("0b_0_1_1_0"               => Literal(Integer, "0b_0_1_1_0")),
            (" "                        => Whitespace),
            ("0o_7_7_7_"                => Literal(Integer, "0o_7_7_7_")),
            (" "                        => Whitespace),
            ("0________0"               => Literal(Integer, "0________0"));
        }
    }

    #[test]
    fn integer_unexpected_digit_range() {
        check! {
            ("0b12345"                  => Literal(Integer, "0b12345")),
            (","                        => Comma),
            ("0o48_19"                  => Literal(Integer, "0o48_19"));
            // There are no unexpected characters in decimal or hexadecimal literals.
            // The first nondigit is either the start of a type suffix, or the first
            // character of the next token.
        Severity::Error:
            (3, 4), (4, 5), (5, 6), (6, 7), (11, 12), (14, 15);
        }
    }

    #[test]
    fn integer_unexpected_nondecimal_termination() {
        check! {
            ("0x"                       => Literal(Integer, "0x")),
            (","                        => Comma),
            ("0b"                       => Literal(Integer, "0b")),
            (","                        => Comma),
            ("0o"                       => Literal(Integer, "0o")),
            (","                        => Comma),
            ("0x_"                      => Literal(Integer, "0x_")),
            (","                        => Comma),
            ("0b_"                      => Literal(Integer, "0b_")),
            (","                        => Comma),
            ("0o_"                      => Literal(Integer, "0o_"));

        Severity::Error:
            (0, 2), (3, 5), (6, 8), (9, 12), (13, 16), (17, 20);
        }
    }

    // TODO: combined errors

    #[test]
    fn integer_type_suffixes() {
        check! {
            // ASCII suffixes
            ("1foo"                     => Literal(Integer, "1", "foo")),
            (" "                        => Whitespace),
            ("42i32"                    => Literal(Integer, "42", "i32")),
            (" "                        => Whitespace),
            // Only words can be suffixes
            ("42"                       => Literal(Integer, "42")),
            ("+"                        => Identifier("+")),
            ("i32"                      => Identifier("i32")),
            (" "                        => Whitespace),
            // Leading zero is not special
            ("0yFFF"                    => Literal(Integer, "0", "yFFF")),
            (" "                        => Whitespace),
            ("0xBREAD"                  => Literal(Integer, "0xB", "READ")),
            (" "                        => Whitespace),
            ("0_o133"                   => Literal(Integer, "0_", "o133")),
            (" "                        => Whitespace),
            // Unicode suffixes
            ("983\u{7206}\u{767A}"      => Literal(Integer, "983", "\u{7206}\u{767A}")),
            (" "                        => Whitespace),
            ("983\\u{7206}\\u{767A}"    => Literal(Integer, "983", "\u{7206}\u{767A}")),
            (" "                        => Whitespace),
            // This is binary literal, not zero with suffix
            ("0b234"                    => Literal(Integer, "0b234"));

        Severity::Error:
            (71, 72), (72, 73), (73, 74);
        }
    }

    #[test]
    fn integer_type_suffixes_invalid() {
        check! {
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers. Note that underscores are treated
            // as a part of the number.
            ("45f\\u{D800}9"            => Literal(Integer, "45", "f\u{FFFD}9")),
            (" "                        => Whitespace),
            ("951_x\u{0}__"             => Literal(Integer, "951_", "x\u{0}__")),
            (" "                        => Whitespace),
            ("0000\\u430\\u443"         => Literal(Integer, "0000", "\u{0430}\u{0443}")),
            (" "                        => Whitespace),
            ("9_x\\u{78}__"             => Literal(Integer, "9_", "x\u{FFFD}__")),
            (" "                        => Whitespace),
            ("542_o\\x10"               => Literal(Integer, "542_", "o\\x10")),
            (" "                        => Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ("0000"                     => Literal(Integer, "0000")),
            ("\u{0}\u{0}"               => Unrecognized),
            (" "                        => Whitespace),
            ("951__"                    => Literal(Integer, "951__")),
            ("\u{0}"                    => Unrecognized),
            ("__"                       => Identifier("__")),
            (" "                        => Whitespace),
            ("9__"                      => Literal(Integer, "9__")),
            ("\\u{DAAA}\\u{78}"         => Unrecognized),
            (" "                        => Whitespace),
            ("542_"                     => Literal(Integer, "542_")),
            ("\\"                       => Unrecognized),
            ("x10"                      => Identifier("x10"));

        Severity::Error:
            ( 3, 11), (18, 19), (28, 31), (33, 36), (40, 46), (54, 55), (63, 65), (71, 72),
            (78, 86), (78, 92), (97, 98);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Floats

    #[test]
    fn float_basic() {
        check! {
            ("0.0"                      => Literal(Float, "0.0")),
            (" "                        => Whitespace),
            ("1.0"                      => Literal(Float, "1.0")),
            (" "                        => Whitespace),
            ("12313.123123121"          => Literal(Float, "12313.123123121")),
            (" "                        => Whitespace),
            ("0.0000000005"             => Literal(Float, "0.0000000005")),
            (" "                        => Whitespace),
            ("0000000.1200000"          => Literal(Float, "0000000.1200000")),
            (" "                        => Whitespace),
            ("56.43453"                 => Literal(Float, "56.43453"));
        }
    }

    #[test]
    fn float_exponential_without_dot() {
        check! {
            ("9e10"                     => Literal(Float, "9e10")),
            (","                        => Comma),
            ("1400e+12313"              => Literal(Float, "1400e+12313")),
            (","                        => Comma),
            ("1400E-2323"               => Literal(Float, "1400E-2323")),
            ("//"                       => Comment),
            ("\n"                       => Whitespace),
            ("0e+0"                     => Literal(Float, "0e+0")),
            (","                        => Comma),
            ("0001E1000"                => Literal(Float, "0001E1000")),
            (","                        => Comma),
            ("0e-0"                     => Literal(Float, "0e-0"));
        }
    }

    #[test]
    fn float_exponential_with_dot() {
        check! {
            ("2.0E10"                   => Literal(Float, "2.0E10")),
            (")"                        => CloseDelim(Paren)),
            ("0.00000e0"                => Literal(Float, "0.00000e0")),
            ("["                        => OpenDelim(Bracket)),
            ("123.456e+789"             => Literal(Float, "123.456e+789")),
            ("}"                        => CloseDelim(Brace)),
            ("11.11E-11"                => Literal(Float, "11.11E-11")),
            ("{"                        => OpenDelim(Brace)),
            ("9363.83929e00434"         => Literal(Float, "9363.83929e00434"));
        }
    }

    #[test]
    fn float_extreme() {
        // Just making sure that scanner does not care about semantics
        check! {
            ("999999999999999999999999.99999999999999" => Literal(Float, "999999999999999999999999.99999999999999")),
            ("\r\n"                                    => Whitespace),
            ("0.0000000000000000000e-9999999999999999" => Literal(Float, "0.0000000000000000000e-9999999999999999")),
            ("\r\n"                                    => Whitespace),
            ("1.2345678901234567890E+1234567890123456" => Literal(Float, "1.2345678901234567890E+1234567890123456")),
            ("\r\n"                                    => Whitespace),
            ("12345678.901234567890E12345678901234567" => Literal(Float, "12345678.901234567890E12345678901234567"));
        }
    }

    #[test]
    fn float_separators() {
        check! {
            ("10_000.000_001"           => Literal(Float, "10_000.000_001")),
            (","                        => Comma),
            ("0______0.5"               => Literal(Float, "0______0.5")),
            (":"                        => Colon),
            ("1_._2"                    => Literal(Float, "1_._2")),
            (","                        => Comma),
            ("3._4_"                    => Literal(Float, "3._4_")),
            (":"                        => Colon),
            ("7___e54"                  => Literal(Float, "7___e54")),
            (","                        => Comma),
            ("3_._1_E_4"                => Literal(Float, "3_._1_E_4")),
            (":"                        => Colon),
            ("0.0e+___4"                => Literal(Float, "0.0e+___4")),
            (","                        => Comma),
            ("0._0E-__5__"              => Literal(Float, "0._0E-__5__"));
        }
    }

    #[test]
    fn float_deny_radix_spec() {
        check! {
            ("0b1e101101"               => Literal(Float, "0b1e101101")),
            ("          "               => Whitespace),
            ("0b01011011.011010"        => Literal(Float, "0b01011011.011010")),
            ("/*      */"               => Comment),
            ("0o7.7"                    => Literal(Float, "0o7.7")),
            ("          "               => Whitespace),
            ("0o77e10"                  => Literal(Float, "0o77e10")),
            ("          "               => Whitespace),
            ("0x00.0E7"                 => Literal(Float, "0x00.0E7")),
            ("          "               => Whitespace),
            ("0x5.1"                    => Literal(Float, "0x5.1")),
            ("          "               => Whitespace),
            ("0o5e+3"                   => Literal(Float, "0o5e+3"));

        Severity::Error:
            (0, 10), (20, 37), (47, 52), (62, 69), (79, 87), (97, 102), (112, 118);
        }
    }

    #[test]
    fn float_missing_numbers() {
        check! {
            ("5._____"                  => Literal(Float, "5._____")),
            (","                        => Comma),
            ("0._"                      => Literal(Float, "0._")),
            (","                        => Comma),
            ("1e___"                    => Literal(Float, "1e___")),
            (","                        => Comma),
            ("5.0E+___"                 => Literal(Float, "5.0E+___")),
            (","                        => Comma),
            ("10e-___"                  => Literal(Float, "10e-___"));

        Severity::Error:
            (2, 7), (10, 11), (14, 17), (23, 26), (31, 34);
        }
    }

    // TODO: combined errors

    #[test]
    fn float_type_suffixes() {
        check! {
            // ASCII suffixes
            ("1.0zog"                       => Literal(Float, "1.0", "zog")),
            (" "                            => Whitespace),
            ("0e+10f32"                     => Literal(Float, "0e+10", "f32")),
            (" "                            => Whitespace),
            // Only words can be suffixes
            ("56e"                          => Literal(Integer, "56", "e")),
            ("="                            => Identifier("=")),
            ("_f64"                         => Identifier("_f64")),
            (" "                            => Whitespace),
            // Unicode suffixes
            ("0.0_\u{7206}\u{767A}"         => Literal(Float, "0.0_", "\u{7206}\u{767A}")),
            (" "                            => Whitespace),
            ("9.6E-7_8\\u{7206}\\u{767A}"   => Literal(Float, "9.6E-7_8", "\u{7206}\u{767A}")),
            (" "                            => Whitespace);
        }
    }

    #[test]
    fn float_type_suffixes_invalid() {
        check! {
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers. Note that underscores are treated
            // as a part of the number.
            ("4.5f\\u{D800}9"               => Literal(Float, "4.5", "f\u{FFFD}9")),
            (" "                            => Whitespace),
            ("9e0_x\u{0}__"                 => Literal(Float, "9e0_", "x\u{0}__")),
            (" "                            => Whitespace),
            ("0.000\\u{430\\u443}"          => Literal(Float, "0.000", "\u{0430}\u{0443}")),
            (" "                            => Whitespace),
            ("9_e\\u{78}__"                 => Literal(Integer, "9_", "e\u{FFFD}__")),
            (" "                            => Whitespace),
            ("50_e+2_o\\\\10"               => Literal(Float, "50_e+2_", "o\\\\10")),
            (" "                            => Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ("00.0"                         => Literal(Float, "00.0")),
            ("\u{0}\u{1}"                   => Unrecognized),
            (" "                            => Whitespace),
            ("9.1_e+5_"                     => Literal(Float, "9.1_e+5_")),
            ("\u{5}"                        => Unrecognized),
            ("__"                           => Identifier("__")),
            (" "                            => Whitespace),
            ("9E1_"                         => Literal(Float, "9E1_")),
            ("\\u{DEAD}\\u{31}"             => Unrecognized),
            (" "                            => Whitespace),
            ("5.0_"                         => Literal(Float, "5.0_")),
            ("\\"                           => Unrecognized),
            ("e10"                          => Identifier("e10"));

        Severity::Error:
            (  4,  12), ( 19,  20), ( 34,  34), ( 36,  36), ( 44,  50), ( 61,  62), ( 62,  63),
            ( 70,  72), ( 81,  82), ( 89,  97), ( 89, 103), (108, 109);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Characters

    #[test]
    fn character_ascii() {
        check! {
            ("'a'"              => Literal(Character, "a")),
            ("   "              => Whitespace),
            ("'b'"              => Literal(Character, "b")),
            ("   "              => Whitespace),
            ("'0'"              => Literal(Character, "0")),
            ("   "              => Whitespace),
            ("'''"              => Literal(Character, "'")),
            ("   "              => Whitespace),
            ("' '"              => Literal(Character, " ")),
            ("   "              => Whitespace),
            ("'''"              => Literal(Character, "'")),
            ("'''"              => Literal(Character, "'")),
            ("'\"'"             => Literal(Character, "\""));
        }
    }

    #[test]
    fn character_unicode() {
        check! {
            // Surrogates are not valid UTF-8 text and should have been reported before.
            // Rust does not even allow placing them into strings.
            ("'\u{0123}'"       => Literal(Character, "\u{0123}")),
            (" "                => Whitespace),
            ("'\u{07F7}'"       => Literal(Character, "\u{07F7}")),
            (" "                => Whitespace),
            ("'\u{10ba}'"       => Literal(Character, "\u{10ba}")),
            (" "                => Whitespace),
            ("'\u{B0e6}'"       => Literal(Character, "\u{B0e6}")),
            (" "                => Whitespace),
            ("'\u{100300}'"     => Literal(Character, "\u{100300}")),
            (" "                => Whitespace),
            ("'\u{0103CA}'"     => Literal(Character, "\u{0103CA}"));
        }
    }

    #[test]
    fn character_control() {
        check! {
            // Control characters can be used in character literals (technically).
            // They can be rendered weirdly by text editors, but we do not care much.
            ("'\0'"             => Literal(Character, "\0")),
            (" "                => Whitespace),
            ("'\t'"             => Literal(Character, "\t")),
            (" "                => Whitespace),
            ("'\x04'"           => Literal(Character, "\x04")),
            (" "                => Whitespace),
            ("'\x08'"           => Literal(Character, "\x08")),
            (" "                => Whitespace),
            ("'\x0B'"           => Literal(Character, "\x0B")),
            (" "                => Whitespace),
            ("'\x7F'"           => Literal(Character, "\x7F")),
            (" "                => Whitespace),
            ("'\u{2028}'"       => Literal(Character, "\u{2028}")),
            (" "                => Whitespace),
            ("'\u{2029}'"       => Literal(Character, "\u{2029}")),
            (" "                => Whitespace),
            ("'\u{0086}'"       => Literal(Character, "\u{0086}")),
            (" "                => Whitespace);
        }
    }

    #[test]
    fn character_escape_sequences() {
        check! {
            (r"'\0'"            => Literal(Character, "\0")),
            (" "                => Whitespace),
            (r"'\t'"            => Literal(Character, "\t")),
            (" "                => Whitespace),
            (r"'\r'"            => Literal(Character, "\r")),
            (" "                => Whitespace),
            (r"'\n'"            => Literal(Character, "\n")),
            (" "                => Whitespace),
            // Backslash alone is okay
            (r"'\'"             => Literal(Character, "\\")),
            (" "                => Whitespace),
            // Escaped one is fine as well
            (r"'\\'"            => Literal(Character, "\\")),
            (" "                => Whitespace),
            // Escaped double-quote can be copy-pasted from strings
            ("'\\\"'"           => Literal(Character, "\""));
        }
    }

    #[test]
    fn character_unicode_escapes() {
        check! {
            (r"'\x00'"          => Literal(Character, "\x00")),
            (r" "               => Whitespace),
            (r"'\x35'"          => Literal(Character, "\x35")),
            (r" "               => Whitespace),
            (r"'\x1f'"          => Literal(Character, "\x1f")),
            (r" "               => Whitespace),
            // \x?? escapes are ASCII-only
            (r"'\xFF'"          => Literal(Character, "\u{FFFD}")),
            (r" "               => Whitespace),
            (r"'\u{12}'"        => Literal(Character, "\u{12}")),
            (r" "               => Whitespace),
            // Surrogates are not valid
            (r"'\u{d799}'"      => Literal(Character, "\u{D799}")),
            (r" "               => Whitespace),
            (r"'\u{D800}'"      => Literal(Character, "\u{FFFD}")),
            (r" "               => Whitespace),
            (r"'\u{DEAD}'"      => Literal(Character, "\u{FFFD}")),
            (r" "               => Whitespace),
            (r"'\u{DFfF}'"      => Literal(Character, "\u{FFFD}")),
            (r" "               => Whitespace),
            (r"'\u{e000}'"      => Literal(Character, "\u{E000}")),
            (r" "               => Whitespace),
            // Non-characters are okay
            (r"'\u{FFFE}'"      => Literal(Character, "\u{FFFE}")),
            (r" "               => Whitespace),
            (r"'\u{fffff}'"     => Literal(Character, "\u{FFFFF}")),
            (r" "               => Whitespace),
            // Private use area is okay
            (r"'\u{F0123}'"     => Literal(Character, "\u{F0123}")),
            (r" "               => Whitespace),
            (r"'\u{0}'"         => Literal(Character, "\u{0}")),
            (r" "               => Whitespace),
            (r"'\u{00000005}'"  => Literal(Character, "\u{5}")),
            (r" "               => Whitespace),
            // Out of range are not okay but they are still scanned over fine
            (r"'\u{99999999}'"  => Literal(Character, "\u{FFFD}")),
            (r" "               => Whitespace),
            (r"'\u{f0f0f0deadbeef00012345}'" => Literal(Character, "\u{FFFD}"));

        Severity::Error:
            ( 22 , 26), ( 49 , 57), (60, 68), (71, 79), (151, 163), (166, 192);
        }
    }

    // We adopt a simple heuristic for the case of missing closing quotes in character literals.
    // If we see a quote on the same line then our incorrect multi-character literal spans between
    // these quotes (it may mean a string with incorrect quotes). If we find no quotes on the line
    // then maybe the quote character is missing after that single character we saw, or maybe that
    // first quote is erroneously placed, or maybe there are several incorrect characters here.
    // As with strings, it's better to not try to guess the meaning of arbitrary invalid sequences.
    // We do not backtrack so we just eat everything up to the line end as an unrecognized token.
    //
    // TODO: shouldn't this be placed near the code that does this? the tests could xref to it.

    #[test]
    fn character_multicharacter_literals() {
        check! {
            ("'ab'"                 => Literal(Character, "\u{FFFD}")),
            (" "                    => Whitespace),
            ("'\u{00E6}\u{0113}'"   => Literal(Character, "\u{FFFD}")),
            (" "                    => Whitespace),
            (r"'\x31\x32'"          => Literal(Character, "\u{FFFD}")),
            (" "                    => Whitespace),
            (r"'\u{123}\u{4567}'"   => Literal(Character, "\u{FFFD}"));

        Severity::Error:
            (0, 4), (5, 11), (12, 22), (23, 40);
        }
    }

    #[test]
    fn character_missing_quotes() {
        check! {
            ("'ab some + thing"     => Unrecognized),
            ("\n"                   => Whitespace),
            ("'''"                  => Literal(Character, "'")),
            ("', more"              => Unrecognized),
            ("\r\n"                 => Whitespace),
            // special case
            ("''"                   => Literal(Character, "\u{FFFD}")),
            (","                    => Comma),
            (" "                    => Whitespace),
            ("."                    => Dot),
            ("'test\rline'"         => Literal(Character, "\u{FFFD}")),
            ("'another\rtest"       => Unrecognized);

        Severity::Error:
            (29, 31), (39, 40), (34, 45), (53, 54);

        Severity::Fatal:
            ( 0, 16), (20, 27), (45, 58);
        }
    }

    #[test]
    fn character_premature_termination() {
        check! { ("'"      => Unrecognized); Severity::Fatal: (0, 1); }
        check! { ("'a"     => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("'\\"    => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("'\t"    => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("'\\x"   => Unrecognized); Severity::Error: (1, 3);
                                             Severity::Fatal: (0, 3); }
        check! { ("'\\y"   => Unrecognized); Severity::Error: (1, 3);
                                             Severity::Fatal: (0, 3); }
        check! { ("'\\u"   => Unrecognized); Severity::Error: (3, 3);
                                             Severity::Fatal: (0, 3); }
        check! { ("'\\u{"  => Unrecognized); Severity::Error: (3, 4);
                                             Severity::Fatal: (0, 4); }
        check! { ("'\\u{}" => Unrecognized); Severity::Error: (3, 5);
                                             Severity::Fatal: (0, 5); }
    }

    #[test]
    fn character_bare_crs_and_line_endings() {
        check! {
            // Bare carrige returns are reported as misplaced restricted characters
            ("'\r'"         => Literal(Character, "\r")),
            (" "            => Whitespace),
            ("'Carr\riage'" => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),
            // But proper line endings are treated as markers of missing closing quotes
            ("'"            => Unrecognized),
            ("\n"           => Whitespace),
            ("' '"          => Literal(Character, " ")),
            (" "            => Whitespace),
            ("'"            => Unrecognized),
            ("\r\n"         => Whitespace),
            ("'"            => Unrecognized);

        Severity::Error:
            ( 1,  2), ( 9, 10), ( 4, 15);

        Severity::Fatal:
            (16, 17), (22, 23), (25, 26);
        }
    }

    #[test]
    fn character_incorrect_unicode_escape_length() {
        check! {
            (r"'\x'"        => Literal(Character, "\u{FFFD}")),
            (r" "           => Whitespace),
            (r"'\x1'"       => Literal(Character, "\u{FFFD}")),
            (r" "           => Whitespace),
            (r"'\x123'"     => Literal(Character, "\u{FFFD}")),
            (r" "           => Whitespace),
            (r"'\u{}'"      => Literal(Character, "\u{FFFD}"));

        Severity::Error:
            (1, 3), (6, 9), (12, 17), (22, 24);
        }
    }

    // A similar heuristic is used for missing curly braces.
    // If character termination quote is seen before a brace, the brace is inserted.
    // If no character termination quote is found until the line ending, the whole literal
    // is considered unrecognized token with an error message about missing brace.
    //
    // TODO: the same as earlier

    #[test]
    fn character_incorrect_unicode_braces() {
        check! {
            (r"'\u{123'"                => Literal(Character, "\u{123}")),
            (r" "                       => Whitespace),
            (r"'\u{'"                   => Literal(Character, "\u{FFFD}")),
            (r" "                       => Whitespace),
            (r"'\u{uiui}'"              => Literal(Character, "\u{FFFD}")),
            (r" "                       => Whitespace),
            (r"'\u{uiui'"               => Literal(Character, "\u{FFFD}")),
            (r" "                       => Whitespace),
            (r"'\u{some long string}'"  => Literal(Character, "\u{FFFD}")),
            (r" "                       => Whitespace),
            (r"'\u{some long string'"   => Literal(Character, "\u{FFFD}")),
            (r" "                       => Whitespace),
            (r"'\u{123, missing"        => Unrecognized),
            ("\n"                       => Whitespace),
            (r"'\u{more missing"        => Unrecognized);

        Severity::Error:
            (  7,   7), ( 12,  13), ( 16,  24), ( 34,  34), ( 27,  34), ( 37,  57), ( 79,  79),
            ( 60,  79), ( 97,  97), ( 82,  97), (114, 114), ( 99, 114);

        Severity::Fatal:
            ( 81,  97), ( 98, 114);
        }
    }

    #[test]
    fn character_unicode_missing_digits() {
        check! {
            (r"'\u'"        => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),
            (r"'\u}'"       => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),
            (r"'\uguu~'"    => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),
            (r"'\ux\uy'"    => Literal(Character, "\u{FFFD}"));

        Severity::Error:
            ( 3,  3), ( 8,  9), (14, 14), (11, 19), (23, 23), (26, 26), (20, 28);
        }
    }

    #[test]
    fn character_unicode_bare_digits() {
        check! {
            (r"'\u0000'"        => Literal(Character, "\u{0}")),
            (" "                => Whitespace),
            (r"'\u9'"           => Literal(Character, "\u{9}")),
            (" "                => Whitespace),
            (r"'\uDEAD'"        => Literal(Character, "\u{FFFD}")),
            (" "                => Whitespace),
            (r"'\u10F0F0'"      => Literal(Character, "\u{10F0F0}")),
            (" "                => Whitespace),
            (r"'\u9999999999'"  => Literal(Character, "\u{FFFD}")),
            (" "                => Whitespace),
            (r"'\u1\u2'"        => Literal(Character, "\u{FFFD}")),
            (" "                => Whitespace);

        Severity::Error:
            ( 3,  7), (12, 13), (18, 22), (16, 22), (27, 33), (38, 48), (36, 48), (53, 54),
            (56, 57), (50, 58);
        }
    }

    #[test]
    fn character_unknown_escapes() {
        check! {
            // Unsupported C escapes
            (r"'\a'"        => Literal(Character, "a")),
            (" "            => Whitespace),
            (r"'\b'"        => Literal(Character, "b")),
            (" "            => Whitespace),
            (r"'\f'"        => Literal(Character, "f")),
            (" "            => Whitespace),
            (r"'\v'"        => Literal(Character, "v")),
            (" "            => Whitespace),
            (r"'\?'"        => Literal(Character, "?")),
            (" "            => Whitespace),

            // Unsupported hell-knows-whats
            (r"'\X9'"       => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),
            (r"'\@'"        => Literal(Character, "@")),
            (" "            => Whitespace),
            ("'\\\u{0430}'" => Literal(Character, "\u{0430}")),
            (" "            => Whitespace),
            (r"'\m\'"       => Literal(Character, "\u{FFFD}")),
            (" "            => Whitespace),

            // Attempts at line-continuation
            ("'\\"          => Unrecognized),
            ("\n"           => Whitespace),
            ("' '"          => Literal(Character, " ")),
            ("  "           => Whitespace),
            ("'\\\r'"       => Literal(Character, "\r")),
            ("  "           => Whitespace),
            ("'foo\\"       => Unrecognized),
            ("\r\n"         => Whitespace),
            ("' '"          => Literal(Character, " ")),
            ("  "           => Whitespace),
            ("'b\\\t\\"     => Unrecognized),
            ("\n\t"         => Whitespace),
            ("'"            => Unrecognized);

        Severity::Error:
            ( 1,  3), ( 6,  8), (11, 13), (16, 18), (21, 23), (26, 28), (25, 30), (32, 34),
            (37, 40), (43, 45), (42, 47), (58, 59), (57, 59), (76, 78);

        Severity::Fatal:
            (48, 50), (62, 67), (74, 79), (81, 82);
        }
    }

    #[test]
    fn character_type_suffixes() {
        check! {
            // Suffixes are words
            ("'x'wide"                      => Literal(Character, "x", "wide")),
            (" "                            => Whitespace),
            ("'\t'ASCII"                    => Literal(Character, "\t", "ASCII")),
            (" "                            => Whitespace),
            ("'\\t'ASCII"                   => Literal(Character, "\t", "ASCII")),
            (" "                            => Whitespace),
            ("'\u{3435}'_"                  => Literal(Character, "\u{3435}", "_")),
            (" "                            => Whitespace),
            // And only words, symbols are not suffixes
            ("'='"                          => Literal(Character, "=")),
            ("="                            => Identifier("=")),
            ("'='"                          => Literal(Character, "=")),
            (" "                            => Whitespace),
            // Unicode suffixes
            ("'\u{1F74}'\u{1F74}"           => Literal(Character, "\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace),
            ("'\\u{1F74}'\\u{1F74}"         => Literal(Character, "\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace);
        }
    }

    #[test]
    fn character_type_suffixes_invalid() {
        check! {
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ("'\\u{EEEE}'\\u{47f}\\u{DAAA}" => Literal(Character, "\u{EEEE}", "\u{047F}\u{FFFD}")),
            (" "                            => Whitespace),
            ("'\\u{EEEE}'b\\u6Fx"           => Literal(Character, "\u{EEEE}", "b\u{FFFD}x")),
            (" "                            => Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ("'0'"                          => Literal(Character, "0")),
            ("\\u0\\u1"                     => Unrecognized),
            ("\t"                           => Whitespace),
            ("'\\u{F000}'"                  => Literal(Character, "\u{F000}")),
            ("\\u{F000}"                    => Unrecognized),
            ("\t"                           => Whitespace),
            ("'f'"                          => Literal(Character, "f")),
            ("\\"                           => Unrecognized),
            ("x"                            => Identifier("x"));

        Severity::Error:
            (17, 25), (39, 41), (37, 41), (48, 49), (51, 52), (46, 52), (63, 71), (75, 76);
        }
    }

    #[test]
    fn character_type_suffixes_after_invalid() {
        check! {
            // Type suffixes are scanned over just fine after invalid characters
            ("'\\u{DADA}'u32"               => Literal(Character, "\u{FFFD}", "u32")),
            (" "                            => Whitespace),
            ("''cc"                         => Literal(Character, "\u{FFFD}", "cc")),
            ("''"                           => Literal(Character, "\u{FFFD}")),
            (" "                            => Whitespace),
            ("'\\u0'_\\u0"                  => Literal(Character, "\u{0}", "_\u{FFFD}")),
            (" "                            => Whitespace),
            ("'\\5'q"                       => Literal(Character, "5", "q")),
            (" "                            => Whitespace),
            ("'\r'foo"                      => Literal(Character, "\r", "foo")),
            (" "                            => Whitespace),
            ("'some'suffix"                 => Literal(Character, "\u{FFFD}", "suffix")),
            (" "                            => Whitespace),
            // But missing quotes are something else
            ("'foo"                         => Unrecognized),
            ("\n"                           => Whitespace),
            ("c32"                          => Identifier("c32")),
            ("\t"                           => Whitespace),
            ("'bar"                         => Unrecognized),
            ("\r\n"                         => Whitespace),
            ("'baz"                         => Unrecognized);

        Severity::Error:
            (  1,  9), ( 14, 16), ( 18, 20), ( 24, 25), ( 29, 30), ( 27, 30), ( 32, 34),
            ( 38, 39), ( 44, 50);

        Severity::Fatal:
            ( 57, 61), ( 66, 70), ( 72, 76);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Strings

    #[test]
    fn string_basic() {
        check! {
            (r#""""#                            => Literal(String, "")),
            (" "                                => Whitespace),
            (r#"'"'"#                           => Literal(Character, "\"")),
            (r#""'""#                           => Literal(String, "'")),
            (" "                                => Whitespace),
            (r#""foo""#                         => Literal(String, "foo")),
            (r#""bar""#                         => Literal(String, "bar")),
            (" "                                => Whitespace),
            (r#""`!@#$%^&*()_+:<>?';[]{}=""#    => Literal(String, "`!@#$%^&*()_+:<>?';[]{}="));
        }
    }

    #[test]
    fn string_unicode() {
        check! {
            ("\"\u{0395}\u{03C9}\u{03C2}\u{03BD}\u{03B5}\""         => Literal(String, "\u{0395}\u{03C9}\u{03C2}\u{03BD}\u{03B5}")),
            (" "                                                    => Whitespace),
            ("\"\u{041A}\u{044E}\u{043C}\u{043A}\u{0443}\""         => Literal(String, "\u{041A}\u{044E}\u{043C}\u{043A}\u{0443}")),
            (" "                                                    => Whitespace),
            ("\"\u{4EE3}\u{3072}\u{5099}\u{9752}\u{8CBB}\""         => Literal(String, "\u{4EE3}\u{3072}\u{5099}\u{9752}\u{8CBB}")),
            (" "                                                    => Whitespace),
            ("\"\u{0627}\u{0644}\u{062D}\u{0643}\u{0648}\u{0645}\"" => Literal(String, "\u{0627}\u{0644}\u{062D}\u{0643}\u{0648}\u{0645}")),
            (" "                                                    => Whitespace),
            ("\"\u{100100}\u{100200}\u{103000}\u{10FEEE}\u{FEFF}\"" => Literal(String, "\u{100100}\u{100200}\u{103000}\u{10FEEE}\u{FEFF}"));
        }
    }

    #[test]
    fn string_escapes() {
        check! {
            // C-style escapes supported by characters
            (r#""\0\t\r\n""#    => Literal(String, "\0\t\r\n")),
            // Double quotes and backslashes must be escaped in strings
            (r#""\\\" \"\\\"""# => Literal(String, "\\\" \"\\\"")),
            // Nulls and tabs can be used unescaped
            ("\"\t\0\t \tx\0\"" => Literal(String, "\t\0\t \tx\0"));
        }
    }

    #[test]
    fn string_unicode_escapes() {
        check! {
            // Strings support both byte escapes...
            (r#""\x00\x3D\x70 \x50\x6E""#       => Literal(String, "\x00\x3D\x70 \x50\x6E")),
            // ...and Unicode escapes...
            (r#""\u{3} \u{12F1E}\u{F0F0}""#     => Literal(String, "\u{3} \u{12F1E}\u{F0F0}")),
            // ...and, as with characters, somewhat care about their semantics.
            (r#""\xFF\xFE\x00\xDE\xAD""#        => Literal(String, "\u{FFFD}\u{FFFD}\x00\u{FFFD}\u{FFFD}")),
            (r#""\u{D900}\u{F0F0F090909}""#     => Literal(String, "\u{FFFD}\u{FFFD}"));

        Severity::Error:
            (49, 53), (53, 57), (61, 65), (65, 69), (71, 79), (79, 94);
        }
    }

    #[test]
    fn string_multiline() {
        check! {
            ("\"multiline\ndemo\""              => Literal(String, "multiline\ndemo")),
            ("\n"                               => Whitespace),
            ("\"windows\r\nline\r\nendings\""   => Literal(String, "windows\nline\nendings")),
            ("\n"                               => Whitespace),
            ("\"bare\rCR character\""           => Literal(String, "bare\rCR character")),
            ("\n"                               => Whitespace),
            ("\"continuation\\\nstring\""       => Literal(String, "continuationstring")),
            ("\n"                               => Whitespace),
            ("\"windows\\\r\ncontinuation\""    => Literal(String, "windowscontinuation")),
            ("\n"                               => Whitespace),
            ("\"cont\\\n\t\t  with space\""     => Literal(String, "contwith space")),
            ("\n"                               => Whitespace),
            ("\"\\\r\n\none more time\""        => Literal(String, "one more time")),
            ("\n"                               => Whitespace),
            ("\"but\\\rbare CR doesn't work\""  => Literal(String, "but\rbare CR doesn't work"));

        Severity::Error:
            (47, 48), (158, 159), (157, 159);
        }
    }

    #[test]
    fn string_premature_termination() {
        check! { ("\""      => Unrecognized); Severity::Fatal: (0, 1); }
        check! { ("\"a"     => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("\"\\"    => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("\"\t"    => Unrecognized); Severity::Fatal: (0, 2); }
        check! { ("\"\\x"   => Unrecognized); Severity::Error: (1, 3);
                                              Severity::Fatal: (0, 3); }
        check! { ("\"\\y"   => Unrecognized); Severity::Error: (1, 3);
                                              Severity::Fatal: (0, 3); }
        check! { ("\"\\u"   => Unrecognized); Severity::Error: (3, 3);
                                              Severity::Fatal: (0, 3); }
        check! { ("\"\\u{"  => Unrecognized); Severity::Error: (3, 4);
                                              Severity::Fatal: (0, 4); }
        check! { ("\"\\u{}" => Unrecognized); Severity::Error: (3, 5);
                                              Severity::Fatal: (0, 5); }
    }

    #[test]
    fn string_incorrect_unicode_escape_length() {
        check! {
            (r#""\x""#     => Literal(String, "\u{FFFD}")),
            (r#" "#        => Whitespace),
            (r#""\x1""#    => Literal(String, "\u{FFFD}")),
            (r#" "#        => Whitespace),
            (r#""\x123""#  => Literal(String, "\u{FFFD}")),
            (r#" "#        => Whitespace),
            (r#""\u{}""#   => Literal(String, "\u{FFFD}"));

        Severity::Error:
            (1, 3), (6, 9), (12, 17), (22, 24);
        }
    }

    #[test]
    fn string_incorrect_unicode_braces() {
        check! {
            (r#""\u{123""#                                  => Literal(String, "\u{123}")),
            (r#" "#                                         => Whitespace),
            (r#""\u{""#                                     => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            (r#""\u{uiui}""#                                => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            (r#""\u{uiui""#                                 => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            (r#""\u{some long string}""#                    => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            (r#""\u{some long string""#                     => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{123, missing\nsome text after that}\""  => Literal(String, "\u{FFFD}\nsome text after that}")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{456, missing\r\nsome more text\""       => Literal(String, "\u{FFFD}\nsome more text")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{and bare carriage\rreturn}\""           => Literal(String, "\u{FFFD}")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{line ends\\\n here}\""                  => Literal(String, "\u{FFFD}here}")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{with this\\u{123}\""                    => Literal(String, "\u{FFFD}\u{123}")),
            (r#" "#                                         => Whitespace),
            ("\"\\u{or this\\f\""                           => Literal(String, "\u{FFFD}f")),
            (r#" "#                                         => Whitespace),
            (r#""\u{check missing"#                         => Unrecognized);

        Severity::Error:
            (  7,   7), ( 12,  13), ( 16,  24), ( 34,  34), ( 27,  34), ( 37,  57), ( 79,  79),
            ( 60,  79), ( 97,  97), ( 82,  97), (137, 137), (122, 137), (156, 184), (199, 199),
            (187, 199), (222, 222), (210, 222), (242, 242), (232, 242), (242, 244), (263, 263),
            (247, 263);

        Severity::Fatal:
            (246, 263);
        }
    }

    #[test]
    fn string_unicode_missing_opening() {
        check! {
            (r#""\u""#      => Literal(String, "\u{FFFD}")),
            (" "            => Whitespace),
            (r#""\u}""#     => Literal(String, "\u{FFFD}")),
            (" "            => Whitespace),
            (r#""\uguu~""#  => Literal(String, "\u{FFFD}guu~")),
            (" "            => Whitespace),
            (r#""\ux\uy""#  => Literal(String, "\u{FFFD}x\u{FFFD}y"));

        Severity::Error:
            (3, 3), (8, 9), (14, 14), (23, 23), (26, 26);
        }
    }

    #[test]
    fn string_unicode_bare_digits() {
        check! {
            (r#""\u0000\u9\uDEAD\u101111\u99999999999\u1}\u""# => Literal(String, "\u{0}\u{9}\u{FFFD}\u{101111}\u{FFFD}\u{1}\u{FFFD}"));

        Severity::Error:
            ( 3,  7), ( 9, 10), (12, 16), (10, 16), (18, 24), (26, 37), (24, 37), (39, 39),
            (43, 43);
        }
    }

    #[test]
    fn string_unknown_escapes() {
        check! {
            // Unsupported C escapes
            ("\"\\a\\b\\f\\v\\?\\'\""   => Literal(String, "abfv?'")),
            // Unsupported hell-knows-whats
            ("\"\\X9\\!\\\u{0742}\\y\"" => Literal(String, "X9!\u{742}y"));

        Severity::Error:
            ( 1,  3), ( 3,  5), ( 5,  7), ( 7,  9), ( 9, 11), (11, 13), (15, 17), (18, 20),
            (20, 23), (23, 25);
        }
    }

    // TODO: more tests

    #[test]
    fn string_type_suffixes() {
        check! {
            // Suffixes are words
            ("\"x\"wide"                    => Literal(String, "x", "wide")),
            (" "                            => Whitespace),
            ("\"\t\"ASCII"                  => Literal(String, "\t", "ASCII")),
            (" "                            => Whitespace),
            ("\"\\t\"ASCII"                 => Literal(String, "\t", "ASCII")),
            (" "                            => Whitespace),
            ("\"\u{3435}\"_"                => Literal(String, "\u{3435}", "_")),
            (" "                            => Whitespace),
            // And only words, symbols are not suffixes
            ("\"=\""                        => Literal(String, "=")),
            ("=="                           => Identifier("==")),
            ("\"=\""                        => Literal(String, "=")),
            (" "                            => Whitespace),
            // Unicode suffixes
            ("\"\u{1F74}\"\u{1F74}"         => Literal(String, "\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace),
            ("\"\\u{1F74}\"\\u{1F74}"       => Literal(String, "\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace);
        }
    }

    #[test]
    fn string_type_suffixes_invalid() {
        check! {
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ("\"fofo\"\\u{47f}\\u{DAAA}"    => Literal(String, "fofo", "\u{047F}\u{FFFD}")),
            ("\"\"b\\u4Fx"                  => Literal(String, "", "b\u{FFFD}x")),
            (" "                            => Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ("\"\\\"\""                     => Literal(String, "\"")),
            ("\\u3F"                        => Unrecognized),
            ("\n"                           => Whitespace),
            ("\"\\u{F000}\\u{D800}\""       => Literal(String, "\u{F000}\u{FFFD}")),
            ("\\u{F000}"                    => Unrecognized),
            ("\t"                           => Whitespace),
            ("\"foo\""                      => Literal(String, "foo")),
            ("\\"                           => Unrecognized),
            ("U900"                         => Identifier("U900"));

        Severity::Error:
            (13, 21), (26, 28), (24, 28), (36, 38), (34, 38), (48, 56), (57, 65), (71, 72);
        }
    }

    #[test]
    fn string_type_suffixes_after_invalid() {
        check! {
            // Type suffixes are scanned over just fine after invalid strings
            ("\"\\u0\"_\\u0"                => Literal(String, "\u{0}", "_\u{FFFD}")),
            (" "                            => Whitespace),
            ("\"\\5\"q"                     => Literal(String, "5", "q")),
            (" "                            => Whitespace),
            ("\"\r\"foo"                    => Literal(String, "\r", "foo")),
            (" "                            => Whitespace),
            ("\"\\x\"zog"                   => Literal(String, "\u{FFFD}", "zog")),
            (" "                            => Whitespace),
            ("\"\\x4500\"__"                => Literal(String, "\u{FFFD}", "__"));
            // We aren't able to test missing quotes as they are detected only at EOF
        Severity::Error:
            ( 3,  4), ( 8,  9), ( 6,  9), (11, 13), (17, 18), (24, 26), (32, 38);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Raw strings

    #[test]
    fn raw_string_basic() {
        check! {
            ("r\"\""               => Literal(RawString, "")),
            (" "                   => Whitespace),
            ("r\"test\""           => Literal(RawString, "test")),
            (" "                   => Whitespace),
            ("r\"h\\a\\-\\h\\a\""  => Literal(RawString, "h\\a\\-\\h\\a"));
        }
    }

    #[test]
    fn raw_string_unicode() {
        check! {
            ("r\"\u{0442}\u{044D}\u{0441}\u{0442}\""                            => Literal(RawString, "\u{0442}\u{044D}\u{0441}\u{0442}")),
            (" "                                                                => Whitespace),
            ("r\"\u{D1F}\u{D46}\u{D38}\u{D4D}\u{D31}\u{D4D}\u{D31}\u{D4D}\""    => Literal(RawString, "\u{D1F}\u{D46}\u{D38}\u{D4D}\u{D31}\u{D4D}\u{D31}\u{D4D}")),
            (" "                                                                => Whitespace),
            ("r\"\u{0074}\u{0068}\u{1EED}\""                                    => Literal(RawString, "\u{0074}\u{0068}\u{1EED}")),
            (" "                                                                => Whitespace),
            ("r\"\u{10E2}\u{10D4}\u{10E1}\u{10E2}\u{10D8}\""                    => Literal(RawString, "\u{10E2}\u{10D4}\u{10E1}\u{10E2}\u{10D8}")),
            (" "                                                                => Whitespace),
            ("r\"\u{100100}\u{100200}\u{103000}\\\u{10FEEE}\u{FEFF}\""          => Literal(RawString, "\u{100100}\u{100200}\u{103000}\\\u{10FEEE}\u{FEFF}"));
        }
    }

    #[test]
    fn raw_string_hashed() {
        check! {
            ("r\"#\""                                           => Literal(RawString, "#")),
            (" "                                                => Whitespace),
            ("r\"##\""                                          => Literal(RawString, "##")),
            (" "                                                => Whitespace),
            ("r#\"\"\"\"#"                                      => Literal(RawString, "\"\"")),
            (" "                                                => Whitespace),
            ("r##\"\"#\"\"##"                                   => Literal(RawString, "\"#\"")),
            (" "                                                => Whitespace),
            ("r###################\"test\"###################"  => Literal(RawString, "test")),
            (" "                                                => Whitespace),
            ("r#\"<img src=\"some\test.jpg\"/>\"#"              => Literal(RawString, "<img src=\"some\test.jpg\"/>"));
        }
    }

    #[test]
    fn raw_string_multiline() {
        check! {
            ("r\"multi\nline\""         => Literal(RawString, "multi\nline")),
            (","                        => Comma),
            ("r\"windows\r\nline\""     => Literal(RawString, "windows\nline")),
            (","                        => Comma),
            ("r\"extra\n\n\npadding\""  => Literal(RawString, "extra\n\n\npadding")),
            (","                        => Comma),
            ("r#\"\"\n\"\n\"#"          => Literal(RawString, "\"\n\"\n")),
            (","                        => Comma),
            ("r##\"\r\n#\r\n\"##"       => Literal(RawString, "\n#\n")),
            (","                        => Comma),
            // These aren't escapes, just some slashes followed by a newline
            ("r\"line\\\nbreak\""       => Literal(RawString, "line\\\nbreak")),
            (","                        => Comma),
            ("r\"more\\\r\nbreak\""     => Literal(RawString, "more\\\nbreak"));
        }
    }

    #[test]
    fn raw_string_invalid_escape_sequences() {
        check! {
            ("r\"\\\""                  => Literal(RawString, "\\")),
            (" "                        => Whitespace),
            ("r\"\\\u{1234}\""          => Literal(RawString, "\\\u{1234}")),
            (" "                        => Whitespace),
            ("r\"\\u{foo}\\u}{\\ufo\""  => Literal(RawString, "\\u{foo}\\u}{\\ufo")),
            (" "                        => Whitespace),
            ("r\"\\.\\9\\/\""           => Literal(RawString, "\\.\\9\\/")),
            (" "                        => Whitespace),
            ("r\"\\xXx\""               => Literal(RawString, "\\xXx")),
            (" "                        => Whitespace),
            ("r\"\\r\\#\\m\""           => Literal(RawString, "\\r\\#\\m"));
        }
    }

    #[test]
    fn raw_string_premature_termination() {
        check! { ("r\""               => Unrecognized); Severity::Fatal: (0, 2);  }
        check! { ("r\"some text"      => Unrecognized); Severity::Fatal: (0, 11); }
        check! { ("r\"line\n"         => Unrecognized); Severity::Fatal: (0, 7);  }
        check! { ("r\"windows\r\n"    => Unrecognized); Severity::Fatal: (0, 11); }
        check! { ("r\"bare CR\r"      => Unrecognized); Severity::Error: (9, 10);
                                                        Severity::Fatal: (0, 10); }
        check! { ("r#\"text\""        => Unrecognized); Severity::Fatal: (0, 8);  }
        check! { ("r###\"te\"#xt\"##" => Unrecognized); Severity::Fatal: (0, 14); }
        check! { ("r#\"r\"\""         => Unrecognized); Severity::Fatal: (0, 6);  }
    }

    #[test]
    fn raw_string_bare_cr() {
        check! {
            ("r\"te\rst\""                  => Literal(RawString, "te\rst")),
            (" "                            => Whitespace),
            ("r\"test\\\r\""                => Literal(RawString, "test\\\r")),
            (" "                            => Whitespace),
            ("r#\"bare\r\r\rCR\"#"          => Literal(RawString, "bare\r\r\rCR"));

        Severity::Error:
            ( 4,  5), (16, 17), (26, 27), (27, 28), (28, 29);
        }
    }

    // TODO: more tests?
    //       Like, unrecognized starts of raw strings, "r#####foo"?
    //       However, maybe these should be parsed as invalid multipart identifiers.

    #[test]
    fn raw_string_type_suffixes() {
        check! {
            // Suffixes are words
            ("r\"x\"wide"                   => Literal(RawString, "x", "wide")),
            (" "                            => Whitespace),
            ("r##\"\t\"##ASCII"             => Literal(RawString, "\t", "ASCII")),
            (" "                            => Whitespace),
            ("r\"\\t\"ASCII"                => Literal(RawString, "\\t", "ASCII")),
            (" "                            => Whitespace),
            ("r#\"\u{3435}\"#_"             => Literal(RawString, "\u{3435}", "_")),
            (" "                            => Whitespace),
            // And only words, symbols are not suffixes
            ("r\"=\""                       => Literal(RawString, "=")),
            ("=="                           => Identifier("==")),
            ("r\"=\""                       => Literal(RawString, "=")),
            (" "                            => Whitespace),
            // Unicode suffixes
            ("r\"\u{1F74}\"\u{1F74}"        => Literal(RawString, "\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace),
            ("r\"\\u{1F74}\"\\u{1F74}"      => Literal(RawString, "\\u{1F74}", "\u{1F74}")),
            (" "                            => Whitespace),
            // Suffixes (like other tokens) are scanned over geedily, but there
            // is an exception for raw strings. In sequences /r"/ and /r#/, the
            // 'r' character is never considered a type suffix. However, it is
            // true only for the *first* 'r'. Everything else is scanned over
            // greedily as usual.
            ("r\"\""                        => Literal(RawString, "")),
            ("r\"\"rr"                      => Literal(RawString, "", "rr")),
            ("\"\""                         => Literal(String, "")),
            (" "                            => Whitespace),
            ("r#\"1\"#"                     => Literal(RawString, "1")),
            ("r##\"x\"##"                   => Literal(RawString, "x")),
            (" "                            => Whitespace),
            ("rawr"                         => Identifier("rawr")),
            ("\"123\""                      => Literal(String, "123")),
            (" "                            => Whitespace),
            ("r\"x\"boar"                   => Literal(RawString, "x", "boar")),
            ("#"                            => Hash),
            ("\"x\""                        => Literal(String, "x")),
            ("#"                            => Hash);
        }
    }

    #[test]
    fn raw_string_type_suffixes_invalid() {
        check! {
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ("r\"fofo\"\\u{47f}\\u{DAAA}"   => Literal(RawString, "fofo", "\u{047F}\u{FFFD}")),
            (" "                            => Whitespace),
            ("r#\"\"#b\\u4Fx"               => Literal(RawString, "", "b\u{FFFD}x")),
            (" "                            => Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ("r\"\\\""                      => Literal(RawString, "\\")),
            ("\\u3F"                        => Unrecognized),
            ("\n"                           => Whitespace),
            ("r##\"\\u{F000}\\u{D800}\"##"  => Literal(RawString, "\\u{F000}\\u{D800}")),
            ("\\u{F000}"                    => Unrecognized),
            ("\t"                           => Whitespace),
            ("r\"foo\""                     => Literal(RawString, "foo")),
            ("\\"                           => Unrecognized),
            ("U900"                         => Identifier("U900")),
            ("\n"                           => Whitespace),
            // Specifically for raw strings: \u{72} is not valid starter for them
            ("r#\"\"#"                      => Literal(RawString, "")),
            ("\\u{72}"                      => Unrecognized),
            ("#"                            => Hash),
            ("\"4\""                        => Literal(String, "4")),
            ("#"                            => Hash);

        Severity::Error:
            (14, 22), (31, 33), (29, 33), (41, 43), (39, 43), (67, 75), (82, 83), (93, 99);
        }
    }

    #[test]
    fn raw_string_type_suffixes_after_invalid() {
        check! {
            // Type suffixes are scanned over just fine after invalid strings
            ("r\"\\u0\"_\\u0"           => Literal(RawString, "\\u0", "_\u{FFFD}")),
            (" "                        => Whitespace),
            ("r##\"\\5\"##q"            => Literal(RawString, "\\5", "q")),
            (" "                        => Whitespace),
            ("r\"\r\"foo"               => Literal(RawString, "\r", "foo"));
            // We aren't able to test missing quotes as they are detected only at EOF
        Severity::Error:
            ( 9, 10), ( 7, 10), (24, 25);
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Identifiers

    #[test]
    fn identifier_ascii_words() {
        check! {
            ("word"             => Identifier("word")),
            (" "                => Whitespace),
            ("_underscore_"     => Identifier("_underscore_")),
            (" "                => Whitespace),
            ("__"               => Identifier("__")),
            (" "                => Whitespace),
            ("x1234567890"      => Identifier("x1234567890")),
            (" "                => Whitespace),
            ("_9_"              => Identifier("_9_")),
            (" "                => Whitespace),
            ("UpperCase"        => Identifier("UpperCase")),
            (" "                => Whitespace),
            ("OMG11111"         => Identifier("OMG11111"));
        }
    }

    #[test]
    fn identifier_ascii_marks() {
        check! {
            ("+"                => Identifier("+")),
            (" "                => Whitespace),
            ("-"                => Identifier("-")),
            (" "                => Whitespace),
            ("*"                => Identifier("*")),
            (" "                => Whitespace),
            ("/"                => Identifier("/")),
            (" "                => Whitespace),
            ("<="               => Identifier("<=")),
            (" "                => Whitespace),
            ("="                => Identifier("=")),
            (" "                => Whitespace),
            ("=="               => Identifier("==")),
            (" "                => Whitespace),
            (".."               => Identifier("..")),
            (" "                => Whitespace),
            ("..."              => Identifier("...")),
            (" "                => Whitespace),
            ("..+..=../..*.."   => Identifier("..+..=../..*..")),
            (" "                => Whitespace),
            ("<$>"              => Identifier("<$>")),
            (" "                => Whitespace),
            ("&&"               => Identifier("&&")),
            (" "                => Whitespace),
            ("??"               => Identifier("??")),
            (" "                => Whitespace),
            ("+++"              => Identifier("+++")),
            (" "                => Whitespace),
            ("%/%"              => Identifier("%/%")),
            (" "                => Whitespace),
            ("<$%&*+|-~/=@^>!?" => Identifier("<$%&*+|-~/=@^>!?"));
        }
    }

    #[test]
    fn identifier_unicode_words() {
        check! {
    // Lu, Ll, Lo
            ("\u{0054}\u{0068}\u{1EED}\u{005F}\u{006E}\u{0067}\u{0068}\u{0069}\u{1EC7}\u{006D}"                 => Identifier("\u{0054}\u{0068}\u{1EED}\u{005F}\u{006E}\u{0067}\u{0068}\u{0069}\u{1EC7}\u{006D}")),
            (" "                                                                                                => Whitespace),
            ("\u{0583}\u{0578}\u{0580}\u{0571}\u{0561}\u{0580}\u{056F}\u{0578}\u{0582}\u{0574}"                 => Identifier("\u{0583}\u{0578}\u{0580}\u{0571}\u{0561}\u{0580}\u{056F}\u{0578}\u{0582}\u{0574}")),
            (" "                                                                                                => Whitespace),
            ("\u{0422}\u{0435}\u{0441}\u{0442}\u{0423}\u{0432}\u{0430}\u{043D}\u{043D}\u{042F}"                 => Identifier("\u{0422}\u{0435}\u{0441}\u{0442}\u{0423}\u{0432}\u{0430}\u{043D}\u{043D}\u{042F}")),
            (" "                                                                                                => Whitespace),
            ("\u{09AA}\u{09B0}\u{09C0}\u{0995}\u{09CD}\u{09B7}\u{09BE}\u{09AE}\u{09C2}\u{09B2}\u{0995}"         => Identifier("\u{09AA}\u{09B0}\u{09C0}\u{0995}\u{09CD}\u{09B7}\u{09BE}\u{09AE}\u{09C2}\u{09B2}\u{0995}")),
            (" "                                                                                                => Whitespace),
            ("\u{691C}\u{67FB}"                                                                                 => Identifier("\u{691C}\u{67FB}")),
            (" "                                                                                                => Whitespace),
            ("\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}"                                                         => Identifier("\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}")),
            (" "                                                                                                => Whitespace),
            ("\u{1780}\u{17B6}\u{179A}\u{1792}\u{17D2}\u{179C}\u{17BE}\u{178F}\u{17C1}\u{179F}\u{17D2}\u{178F}" => Identifier("\u{1780}\u{17B6}\u{179A}\u{1792}\u{17D2}\u{179C}\u{17BE}\u{178F}\u{17C1}\u{179F}\u{17D2}\u{178F}")),
            (" "                                                                                                => Whitespace),
    // Lt
            ("\u{01F2}\u{0061}\u{0031}"                                                                         => Identifier("\u{01F2}\u{0061}\u{0031}")),
            (" "                                                                                                => Whitespace),
            ("\u{1FAA}"                                                                                         => Identifier("\u{1FAA}")),
            (" "                                                                                                => Whitespace),
    // Lm
            ("\u{1D2E}\u{1D43}\u{1D48}"                                                                         => Identifier("\u{1D2E}\u{1D43}\u{1D48}")),
            (" "                                                                                                => Whitespace),
            ("\u{02C7}\u{02E4}\u{06E6}"                                                                         => Identifier("\u{02C7}\u{02E4}\u{06E6}")),
            (" "                                                                                                => Whitespace),
    // Nl
            ("\u{2169}\u{216C}\u{2164}"                                                                         => Identifier("\u{2169}\u{216C}\u{2164}")),
            (" "                                                                                                => Whitespace),
            ("\u{3007}\u{3007}\u{3007}"                                                                         => Identifier("\u{3007}\u{3007}\u{3007}")),
            (" "                                                                                                => Whitespace),
            ("\u{12461}\u{12468}"                                                                               => Identifier("\u{12461}\u{12468}")),
            (" "                                                                                                => Whitespace),
    // Other_ID_Start
            ("\u{2118}\u{212E}"                                                                                 => Identifier("\u{2118}\u{212E}")),
            (" "                                                                                                => Whitespace),
            ("\u{212E}\u{2118}"                                                                                 => Identifier("\u{212E}\u{2118}")),
            (" "                                                                                                => Whitespace),
    // Mn (continue)
            ("\u{0043}\u{0364}\u{0348}\u{0359}\u{0345}\u{032E}\u{0323}\u{035A}\u{0074}\u{0342}\u{0351}\u{0351}\u{0309}\
              \u{0363}\u{0301}\u{035E}\u{0331}\u{0325}\u{032A}\u{034E}\u{0329}\u{031E}\u{0068}\u{035F}\u{0075}\u{0368}\
              \u{0365}\u{0359}\u{006C}\u{036E}\u{0307}\u{0358}\u{031E}\u{0356}\u{0329}\u{0330}\u{0326}\u{0068}\u{0351}\
              \u{030C}\u{0312}\u{0367}\u{033C}\u{035A}\u{0075}\u{0350}\u{034A}\u{036E}\u{0336}\u{0329}\u{0320}\u{031E}"
            => Identifier(
             "\u{0043}\u{0364}\u{0348}\u{0359}\u{0345}\u{032E}\u{0323}\u{035A}\u{0074}\u{0342}\u{0351}\u{0351}\u{0309}\
              \u{0363}\u{0301}\u{035E}\u{0331}\u{0325}\u{032A}\u{034E}\u{0329}\u{031E}\u{0068}\u{035F}\u{0075}\u{0368}\
              \u{0365}\u{0359}\u{006C}\u{036E}\u{0307}\u{0358}\u{031E}\u{0356}\u{0329}\u{0330}\u{0326}\u{0068}\u{0351}\
              \u{030C}\u{0312}\u{0367}\u{033C}\u{035A}\u{0075}\u{0350}\u{034A}\u{036E}\u{0336}\u{0329}\u{0320}\u{031E}")),
            (" " => Whitespace),
    // Mc (continue)
            ("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}"                                                         => Identifier("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}")),
            (" "                                                                                                => Whitespace),
            ("\u{0932}\u{0902}\u{092C}\u{0947}\u{005F}\u{0938}\u{092E}\u{092F}\u{005F}\u{0924}\u{0915}"         => Identifier("\u{0932}\u{0902}\u{092C}\u{0947}\u{005F}\u{0938}\u{092E}\u{092F}\u{005F}\u{0924}\u{0915}")),
            (" "                                                                                                => Whitespace),
    // Nd (continue)
            ("\u{005F}\u{0661}\u{0665}"                                                                         => Identifier("\u{005F}\u{0661}\u{0665}")),
            (" "                                                                                                => Whitespace),
            ("\u{0996}\u{09BE}\u{09A6}\u{09CD}\u{09AF}\u{09E7}\u{0AE7}\u{0DE9}\u{1040}\u{A8D6}"                 => Identifier("\u{0996}\u{09BE}\u{09A6}\u{09CD}\u{09AF}\u{09E7}\u{0AE7}\u{0DE9}\u{1040}\u{A8D6}")),
            (" "                                                                                                => Whitespace),
    // Pc (continue)
            ("\u{0061}\u{203F}\u{0062}"                                                                         => Identifier("\u{0061}\u{203F}\u{0062}")),
            (" "                                                                                                => Whitespace),
            ("\u{0078}\u{FE4D}\u{0079}"                                                                         => Identifier("\u{0078}\u{FE4D}\u{0079}")),
            (" "                                                                                                => Whitespace),
            ("\u{005F}\u{FE4F}\u{005F}"                                                                         => Identifier("\u{005F}\u{FE4F}\u{005F}")),
            (" "                                                                                                => Whitespace),
    // Other_ID_Continue
            ("\u{0057}\u{00B7}\u{006F}\u{00B7}\u{0057}"                                                         => Identifier("\u{0057}\u{00B7}\u{006F}\u{00B7}\u{0057}")),
            (" "                                                                                                => Whitespace),
            ("\u{1213}\u{121F}\u{1226}\u{1369}\u{136A}\u{136B}\u{136C}\u{136D}\u{136E}\u{136F}\u{1370}\u{1371}" => Identifier("\u{1213}\u{121F}\u{1226}\u{1369}\u{136A}\u{136B}\u{136C}\u{136D}\u{136E}\u{136F}\u{1370}\u{1371}")),
            (" "                                                                                                => Whitespace),
            ("\u{03A4}\u{0387}\u{03C1}\u{0387}\u{03BF}\u{0387}\u{03C6}\u{0387}\u{03AE}\u{0387}"                 => Identifier("\u{03A4}\u{0387}\u{03C1}\u{0387}\u{03BF}\u{0387}\u{03C6}\u{0387}\u{03AE}\u{0387}")),
            (" "                                                                                                => Whitespace),
            ("\u{0078}\u{19DA}"                                                                                 => Identifier("\u{0078}\u{19DA}")),
            (" "                                                                                                => Whitespace),
    // ZWJ, ZWNJ
            ("\u{0CA8}\u{0CCD}\u{0CA8}"                                                                         => Identifier("\u{0CA8}\u{0CCD}\u{0CA8}")),
            (" "                                                                                                => Whitespace),
            ("\u{0CA8}\u{0CCD}\u{200C}\u{0CA8}"                                                                 => Identifier("\u{0CA8}\u{0CCD}\u{200C}\u{0CA8}")),
            (" "                                                                                                => Whitespace),
            ("\u{0915}\u{094D}\u{0937}"                                                                         => Identifier("\u{0915}\u{094D}\u{0937}")),
            (" "                                                                                                => Whitespace),
            ("\u{0915}\u{094D}\u{200D}\u{0937}"                                                                 => Identifier("\u{0915}\u{094D}\u{200D}\u{0937}")),
            (" "                                                                                                => Whitespace),
            ("\u{0645}\u{06CC}\u{200C}\u{062E}\u{0648}\u{0627}\u{0647}\u{0645}"                                 => Identifier("\u{0645}\u{06CC}\u{200C}\u{062E}\u{0648}\u{0627}\u{0647}\u{0645}"));
        }
    }

    #[test]
    fn identifier_unicode_marks() {
        check! {
    // Pd
            ("\u{2015}\u{301C}\u{FE31}\u{2010}\u{30A0}"                 => Identifier("\u{2015}\u{301C}\u{FE31}\u{2010}\u{30A0}")),
            (" "                                                        => Whitespace),
    // Po
            ("\u{00B6}\u{066A}\u{1364}"                                 => Identifier("\u{00B6}\u{066A}\u{1364}")),
            (" "                                                        => Whitespace),
            ("\u{2042}\u{2037}\u{203B}"                                 => Identifier("\u{2042}\u{2037}\u{203B}")),
            (" "                                                        => Whitespace),
            ("\u{203C}\u{A8CE}\u{FE60}\u{FF0A}"                         => Identifier("\u{203C}\u{A8CE}\u{FE60}\u{FF0A}")),
            (" "                                                        => Whitespace),
            ("\u{110BB}\u{111DD}\u{115C9}"                              => Identifier("\u{110BB}\u{111DD}\u{115C9}")),
            (" "                                                        => Whitespace),
            ("\u{2025}"                                                 => Identifier("\u{2025}")),
            (" "                                                        => Whitespace),
            ("\u{2026}"                                                 => Identifier("\u{2026}")),
            (" "                                                        => Whitespace),
    // Sc
            ("\u{00A2}\u{00A5}\u{20A1}\u{0BF9}\u{20B8}\u{FE69}\u{FF04}" => Identifier("\u{00A2}\u{00A5}\u{20A1}\u{0BF9}\u{20B8}\u{FE69}\u{FF04}")),
            (" "                                                        => Whitespace),
    // Sm
            ("\u{00D7}\u{207C}"                                         => Identifier("\u{00D7}\u{207C}")),
            (" "                                                        => Whitespace),
            ("\u{2192}\u{2192}\u{2194}"                                 => Identifier("\u{2192}\u{2192}\u{2194}")),
            (" "                                                        => Whitespace),
            ("\u{220F}\u{2230}"                                         => Identifier("\u{220F}\u{2230}")),
            (" "                                                        => Whitespace),
            ("\u{2257}"                                                 => Identifier("\u{2257}")),
            (" "                                                        => Whitespace),
            ("\u{229D}\u{2AF7}\u{2AF5}"                                 => Identifier("\u{229D}\u{2AF7}\u{2AF5}")),
            (" "                                                        => Whitespace),
    // So
            ("\u{00A9}\u{06DE}\u{0BF5}"                                 => Identifier("\u{00A9}\u{06DE}\u{0BF5}")),
            (" "                                                        => Whitespace),
            ("\u{19FB}\u{19FF}"                                         => Identifier("\u{19FB}\u{19FF}")),
            (" "                                                        => Whitespace),
            ("\u{2127}\u{21B5}\u{21BA}"                                 => Identifier("\u{2127}\u{21B5}\u{21BA}")),
            (" "                                                        => Whitespace),
            ("\u{2375}\u{236A}\u{2361}\u{2360}"                         => Identifier("\u{2375}\u{236A}\u{2361}\u{2360}")),
            (" "                                                        => Whitespace),
            ("\u{2569}\u{2566}\u{2573}\u{2588}"                         => Identifier("\u{2569}\u{2566}\u{2573}\u{2588}")),
            (" "                                                        => Whitespace),
            ("\u{25E9}\u{2625}\u{2639}\u{265B}\u{2690}"                 => Identifier("\u{25E9}\u{2625}\u{2639}\u{265B}\u{2690}")),
            (" "                                                        => Whitespace),
            ("\u{26B5}\u{1D1E7}"                                        => Identifier("\u{26B5}\u{1D1E7}")),
            (" "                                                        => Whitespace),
            ("\u{1D332}\u{1D354}\u{1D940}"                              => Identifier("\u{1D332}\u{1D354}\u{1D940}")),
            (" "                                                        => Whitespace),
            ("\u{1F300}\u{1F401}\u{1F423}\u{1F4B3}\u{1F980}"            => Identifier("\u{1F300}\u{1F401}\u{1F423}\u{1F4B3}\u{1F980}")),
            (" "                                                        => Whitespace),
    // Mc (continue)
            ("\u{0021}\u{17BF}\u{0026}\u{0DDB}\u{002A}\u{0CCB}"         => Identifier("\u{0021}\u{17BF}\u{0026}\u{0DDB}\u{002A}\u{0CCB}")),
            (" "                                                        => Whitespace),
    // Me (continue)
            ("\u{0024}\u{0488}"                                         => Identifier("\u{0024}\u{0488}")),
            (" "                                                        => Whitespace),
            ("\u{003C}\u{20DD}\u{003E}\u{20DE}"                         => Identifier("\u{003C}\u{20DD}\u{003E}\u{20DE}")),
            (" "                                                        => Whitespace),
            ("\u{0021}\u{20DF}"                                         => Identifier("\u{0021}\u{20DF}")),
            (" "                                                        => Whitespace),
    // Mn (continue)
            ("\u{227A}\u{0307}\u{0301}\u{0301}\u{030D}\u{030C}\u{0311}\u{033C}\u{0353}\u{0359}\
              \u{2203}\u{034F}\u{0317}\u{2202}\u{0363}\u{036B}\u{0342}\u{0342}\u{035B}\u{031A}\
              \u{0317}\u{033C}\u{0356}\u{031C}\u{0323}\u{2200}\u{033B}\u{033C}\u{222D}\u{030E}\
              \u{030F}\u{032D}\u{033A}"
            => Identifier(
             "\u{227A}\u{0307}\u{0301}\u{0301}\u{030D}\u{030C}\u{0311}\u{033C}\u{0353}\u{0359}\
              \u{2203}\u{034F}\u{0317}\u{2202}\u{0363}\u{036B}\u{0342}\u{0342}\u{035B}\u{031A}\
              \u{0317}\u{033C}\u{0356}\u{031C}\u{0323}\u{2200}\u{033B}\u{033C}\u{222D}\u{030E}\
              \u{030F}\u{032D}\u{033A}"));
        }
    }

    #[test]
    fn identifier_unicode_delimiters() {
        check! {
    // Ps
            ("\u{2045}"     => Identifier("\u{2045}")),
            (" "            => Whitespace),
            ("\u{2768}"     => Identifier("\u{2768}")),
            (" "            => Whitespace),
            ("\u{2774}"     => Identifier("\u{2774}")),
            (" "            => Whitespace),
            ("\u{300E}"     => Identifier("\u{300E}")),
            (" "            => Whitespace),
            ("\u{FE3D}"     => Identifier("\u{FE3D}")),
            (" "            => Whitespace),
            ("\u{FE5D}"     => Identifier("\u{FE5D}")),
            (" "            => Whitespace),
            ("\u{2987}"     => Identifier("\u{2987}")),
            (" "            => Whitespace),
            ("\u{3008}"     => Identifier("\u{3008}")),
            (" "            => Whitespace),
    // Pe
            ("\u{0F3B}"     => Identifier("\u{0F3B}")),
            (" "            => Whitespace),
            ("\u{0F3D}"     => Identifier("\u{0F3D}")),
            (" "            => Whitespace),
            ("\u{276B}"     => Identifier("\u{276B}")),
            (" "            => Whitespace),
            ("\u{300B}"     => Identifier("\u{300B}")),
            (" "            => Whitespace),
            ("\u{FE18}"     => Identifier("\u{FE18}")),
            (" "            => Whitespace),
            ("\u{FF63}"     => Identifier("\u{FF63}")),
            (" "            => Whitespace),
            ("\u{2992}"     => Identifier("\u{2992}")),
            (" "            => Whitespace),
    // Pi
            ("\u{00AB}"     => Identifier("\u{00AB}")),
            (" "            => Whitespace),
            ("\u{201B}"     => Identifier("\u{201B}")),
            (" "            => Whitespace),
            ("\u{2E02}"     => Identifier("\u{2E02}")),
            (" "            => Whitespace),
            ("\u{2E09}"     => Identifier("\u{2E09}")),
            (" "            => Whitespace),
            ("\u{2E1C}"     => Identifier("\u{2E1C}")),
            (" "            => Whitespace),
            ("\u{2E20}"     => Identifier("\u{2E20}")),
            (" "            => Whitespace),
    // Pf
            ("\u{00BB}"     => Identifier("\u{00BB}")),
            (" "            => Whitespace),
            ("\u{2E03}"     => Identifier("\u{2E03}")),
            (" "            => Whitespace),
            ("\u{203A}"     => Identifier("\u{203A}")),
            (" "            => Whitespace),
            ("\u{2E21}"     => Identifier("\u{2E21}")),
            (" "            => Whitespace),
            ("\u{2019}"     => Identifier("\u{2019}"));
        }
    }

    #[test]
    fn identifier_escape_basic() {
        check! {
            (r"\u{0442}\u{0435}\u{0441}\u{0442}"            => Identifier("\u{0442}\u{0435}\u{0441}\u{0442}")),
            (" "                                            => Whitespace),
            (r"\u{01CB}\u{114D1}\u{114D2}\u{114D3}"         => Identifier("\u{01CB}\u{114D1}\u{114D2}\u{114D3}")),
            (" "                                            => Whitespace),
            (r"\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}"    => Identifier("\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}")),
            (" "                                            => Whitespace),
            (r"\u{2026}\u{2026}\u{2026}"                    => Identifier("\u{2026}\u{2026}\u{2026}")),
            (" "                                            => Whitespace),
            (r"\u{00A9}\u{06DE}\u{0BF5}"                    => Identifier("\u{00A9}\u{06DE}\u{0BF5}")),
            (" "                                            => Whitespace),
            (r"demo\u{Ff11}\u{ff12}\u{fF13}"                => Identifier("demo\u{Ff11}\u{ff12}\u{fF13}")),
            (" "                                            => Whitespace),
            ("\u{041F}\u{0440}\\u{043E}\u{0432}\u{0435}\\u{0440}\u{043A}\\u{0430}" => Identifier("\u{041F}\u{0440}\u{043E}\u{0432}\u{0435}\u{0440}\u{043A}\u{0430}")),
            (" "                                            => Whitespace),
            ("!\\u{20DF}"                                   => Identifier("!\u{20DF}"));
        }
    }

    #[test]
    fn identifier_boundary_rules() {
        check! {
    // Word | Mark
            ("a"                                            => Identifier("a")),
            ("/"                                            => Identifier("/")),
            ("b"                                            => Identifier("b")),
            (" "                                            => Whitespace),
            ("x9"                                           => Identifier("x9")),
            (".."                                           => Identifier("..")),
            ("y"                                            => Identifier("y")),
            (" "                                            => Whitespace),
            ("*"                                            => Identifier("*")),
            ("_"                                            => Identifier("_")),
            ("*"                                            => Identifier("*")),
            (" "                                            => Whitespace),
            ("\u{03BD}\u{03B5}\u{03C1}\u{03CC}"             => Identifier("\u{03BD}\u{03B5}\u{03C1}\u{03CC}")),
            ("\u{002B}"                                     => Identifier("\u{002B}")),
            ("\u{03C6}\u{03C9}\u{03C4}\u{03B9}\u{03AC}"     => Identifier("\u{03C6}\u{03C9}\u{03C4}\u{03B9}\u{03AC}")),
            (" "                                            => Whitespace),
            ("\u{221A}"                                     => Identifier("\u{221A}")),
            ("\u{0078}"                                     => Identifier("\u{0078}")),
            (" "                                            => Whitespace),
            ("\u{222D}"                                     => Identifier("\u{222D}")),
            ("\u{092E}\u{094C}\u{091C}\u{093C}\u{093E}"     => Identifier("\u{092E}\u{094C}\u{091C}\u{093C}\u{093E}")),
            (" "                                            => Whitespace),
            ("\u{29BF}"                                     => Identifier("\u{29BF}")),
            ("\u{006F}"                                     => Identifier("\u{006F}")),
            ("\u{29BF}"                                     => Identifier("\u{29BF}")),
            (" "                                            => Whitespace),
            ("<"                                            => Identifier("<")),
            ("pre\u{0301}sident"                            => Identifier("pre\u{0301}sident")),
            (">"                                            => Identifier(">")),
            (" "                                            => Whitespace),
            ("\u{003D}\u{033F}"                             => Identifier("\u{003D}\u{033F}")),
            ("\u{0078}\u{033F}"                             => Identifier("\u{0078}\u{033F}")),
            ("\u{003D}\u{033F}"                             => Identifier("\u{003D}\u{033F}")),
            ("\n"                                           => Whitespace),
    // Word | Quote
            ("\u{00AB}"                                     => Identifier("\u{00AB}")),
            ("word"                                         => Identifier("word")),
            ("\u{00BB}"                                     => Identifier("\u{00BB}")),
            (" "                                            => Whitespace),
            ("\u{3008}"                                     => Identifier("\u{3008}")),
            ("x"                                            => Identifier("x")),
            ("|"                                            => Identifier("|")),
            ("y"                                            => Identifier("y")),
            ("\u{3009}"                                     => Identifier("\u{3009}")),
            (" "                                            => Whitespace),
            ("\u{FE43}"                                     => Identifier("\u{FE43}")),
            ("\u{3060}\u{307E}\u{3057}\u{307E}\u{3059}"     => Identifier("\u{3060}\u{307E}\u{3057}\u{307E}\u{3059}")),
            ("\u{FE44}"                                     => Identifier("\u{FE44}")),
            ("\n"                                           => Whitespace),
    // Mark | Quote
            ("\u{0F3A}"                                     => Identifier("\u{0F3A}")),
            ("\u{2015}"                                     => Identifier("\u{2015}")),
            ("\u{0F3B}"                                     => Identifier("\u{0F3B}")),
            (" "                                            => Whitespace),
            ("\u{00A5}"                                     => Identifier("\u{00A5}")),
            ("\u{301D}"                                     => Identifier("\u{301D}")),
            ("\u{00A5}"                                     => Identifier("\u{00A5}")),
            (" "                                            => Whitespace),
            ("\u{228F}\u{0BC6}"                             => Identifier("\u{228F}\u{0BC6}")),
            ("\u{FE5D}"                                     => Identifier("\u{FE5D}")),
            (" "                                            => Whitespace),
            ("\u{FE3E}"                                     => Identifier("\u{FE3E}")),
            ("\u{27A4}"                                     => Identifier("\u{27A4}")),
            ("\u{FE3E}"                                     => Identifier("\u{FE3E}")),
            (" "                                            => Whitespace),
            ("\u{1F39B}\u{20E3}"                            => Identifier("\u{1F39B}\u{20E3}")),
            ("\u{2E21}"                                     => Identifier("\u{2E21}")),
            ("\u{1F39B}\u{20E3}"                            => Identifier("\u{1F39B}\u{20E3}")),
            ("\n"                                           => Whitespace),
    // Quote | Quote
            ("\u{201D}"                                     => Identifier("\u{201D}")),
            ("\u{201D}"                                     => Identifier("\u{201D}")),
            ("\u{00AB}"                                     => Identifier("\u{00AB}")),
            ("\u{00AB}"                                     => Identifier("\u{00AB}")),
            ("\u{2039}"                                     => Identifier("\u{2039}")),
            ("\u{203A}"                                     => Identifier("\u{203A}")),
            (" "                                            => Whitespace),
            ("\u{2E21}"                                     => Identifier("\u{2E21}")),
            ("\u{2045}"                                     => Identifier("\u{2045}")),
            ("\u{2770}"                                     => Identifier("\u{2770}")),
            ("\u{2770}"                                     => Identifier("\u{2770}")),
            ("\u{0F3D}"                                     => Identifier("\u{0F3D}")),
            ("\u{276F}"                                     => Identifier("\u{276F}")),
            ("\u{300F}"                                     => Identifier("\u{300F}"));
        }
    }

    #[test]
    fn identifier_boundary_rules_escapes() {
        check! {
    // Word | Mark
            (r"a"                                           => Identifier("a")),
            (r"\u{2215}"                                    => Identifier("\u{2215}")),
            (r"b"                                           => Identifier("b")),
            (" "                                            => Whitespace),
            ("\\u{29BF}"                                    => Identifier("\u{29BF}")),
            ("\u{03BF}"                                     => Identifier("\u{03BF}")),
            ("\\u{29BF}"                                    => Identifier("\u{29BF}")),
            ("\n"                                           => Whitespace),
    // Word | Quote
            (r"\u{00AB}"                                    => Identifier("\u{00AB}")),
            (r"w\u{2113}\u{1d466}d"                         => Identifier("w\u{2113}\u{1D466}d")),
            ("\u{00BB}"                                     => Identifier("\u{00BB}")),
            ("\n"                                           => Whitespace),
    // Mark | Quote
            ("\\u{1F39B}\u{20E3}"                           => Identifier("\u{1F39B}\u{20E3}")),
            ("\u{2E21}"                                     => Identifier("\u{2E21}")),
            ("\u{1F39B}\\u{20E3}"                           => Identifier("\u{1F39B}\u{20E3}")),
            ("\n"                                           => Whitespace),
    // Quote | Quote
            ("\u{2E21}"                                     => Identifier("\u{2E21}")),
            ("\\u{2045}"                                    => Identifier("\u{2045}")),
            ("\u{2770}"                                     => Identifier("\u{2770}"));
        }
    }

    #[test]
    fn identifier_escape_missing_braces() {
        check! {
            // One can get away with just error messages when there are no braces
            // around otherwise correct scalar values
            (r"\u0442\u0435\u0441\u0442"                => Identifier("\u{0442}\u{0435}\u{0441}\u{0442}")),
            (" "                                        => Whitespace),
            ("\\u1794\u{17C3}\\u178F\\u{1784}"          => Identifier("\u{1794}\u{17C3}\u{178F}\u{1784}")),
            (" "                                        => Whitespace),
            // Even boundary detection rules work in this case
            (r"\u212f}"                                 => Identifier("\u{212F}")),
            (r"\u2212}"                                 => Identifier("\u{2212}")),
            (r"\u2134}"                                 => Identifier("\u{2134}")),
            (" "                                        => Whitespace),
            (r"\u276E"                                  => Identifier("\u{276E}")),
            (r"\u{72D7}"                                => Identifier("\u{72D7}")),
            (r"\u300B"                                  => Identifier("\u{300B}")),
            (" "                                        => Whitespace),
            // Given correct scalar values, we can also cope with missing starting/closing brace
            (r"\u{221B\u2192}\u2192\u{2192\u2192"       => Identifier("\u{221B}\u{2192}\u{2192}\u{2192}\u{2192}")),
            (" "                                        => Whitespace),
            // However, if the starting Unicode escape is invalid, it is simply skipped over
            (r"\u"                                      => Unrecognized),
            (r"!"                                       => Identifier("!")),
            (" "                                        => Whitespace),
            (r"\u"                                      => Unrecognized),
            (r"g"                                       => Identifier("g")),
            (" "                                        => Whitespace),
            (r"\u{}"                                    => Unrecognized),
            (r"=="                                      => Identifier("==")),
            (" "                                        => Whitespace),
            (r"\u"                                      => Unrecognized),
            ("::"                                       => Dualcolon),
            (" "                                        => Whitespace),
            (r"\u"                                      => Unrecognized),
            ("]"                                        => CloseDelim(Bracket)),
            (" "                                        => Whitespace),
            ("\\u"                                      => Unrecognized),
            ("\u{301b}"                                 => Identifier("\u{301B}")),
            (" "                                        => Whitespace),
            (r"\u"                                      => Unrecognized),
            (r"\u{301b}"                                => Identifier("\u{301B}")),
            (" "                                        => Whitespace),
            // As in characters, line endings are used to detect missing closing braces
            (r"\u{30C7}\u{30E2}\u{308"                  => Identifier("\u{30C7}\u{30E2}\u{0308}")),
            ("\n"                                       => Whitespace),
            // And unexpected EOFs can happen with identifiers too, thought they are not fatal
            (r"\u{914"                                  => Identifier("\u{0914}"));

        Severity::Error:
            (  2,   6), (  8,  12), ( 14,  18), ( 20,  24), ( 27,  31), ( 36,  40), ( 51,  51),
            ( 58,  58), ( 65,  65), ( 73,  77), ( 87,  91), ( 99,  99), (101, 101), (108, 112),
            (119, 119), (121, 125), (128, 128), (126, 128), (132, 132), (130, 132), (136, 138),
            (134, 138), (143, 143), (141, 143), (148, 148), (146, 148), (152, 152), (150, 152),
            (158, 158), (156, 158), (189, 189), (196, 196);
        }
    }

    #[test]
    fn identifier_escape_invalid_values() {
        check! {
            // As in characters or strings, missing values, surrogate code points, out-or-range
            // values, and non-scalar values are not okay
            ("fo\\u{}o"                                     => Identifier("fo\u{FFFD}o")),
            (" "                                            => Whitespace),
            ("bar\\u{D900}"                                 => Identifier("bar\u{FFFD}")),
            (" "                                            => Whitespace),
            ("b\\u{9999999999}az"                           => Identifier("b\u{FFFD}az")),
            (" "                                            => Whitespace),
            ("D\\u{COMBINING ACUTE ACCENT}mo"               => Identifier("D\u{FFFD}mo")),
            ("\n"                                           => Whitespace),
            // For boundary detection these are treated as valid values in whatever context we are
            (r"\u{D800}\u{DDDD}"                            => Unrecognized),
            (r"_1\u{DFFF}"                                  => Identifier("_1\u{FFFD}")),
            (r"+\u{DEAD}\u{D912}"                           => Identifier("+\u{FFFD}\u{FFFD}")),
            (r"\u{2985}"                                    => Identifier("\u{2985}")),
            (r" "                                           => Whitespace),
            (r"\u{9999999999999}"                           => Unrecognized),
            (r"==\u{Fo fo fo!}\u{a7}"                       => Identifier("==\u{FFFD}\u{00A7}")),
            ("\n"                                           => Whitespace),
            // But invalid values are not start codes. For example, an entirely invalid sequence
            // will not count as an identifier. The digits that immediately follow it are a part
            // of a number, they do not count as XID_Continue which magically converts the whole
            // thing into a word identifier. The scanner never backtracks.
            (r"\u{Some}\u{Invalid}\u{Stuff}"                => Unrecognized),
            (r"123"                                         => Literal(Integer, "123")),
            (r" "                                           => Whitespace),
            (r"\u{Some}\u{Invalid}\u{Stuff}"                => Unrecognized),
            (r"_123"                                        => Identifier("_123"));

        Severity::Error:
            (  4,   6), ( 11,  19), ( 21,  35), ( 39,  65), ( 68,  76), ( 76,  84), ( 68,  84),
            ( 86,  94), ( 95, 103), (103, 111), (120, 137), (120, 137), (139, 152), (159, 167),
            (167, 178), (178, 187), (159, 187), (191, 199), (199, 210), (210, 219), (191, 219);
        }
    }

    #[test]
    fn identifier_invalid_characters_plain() {
        check! {
            // Arbitrary Unicode character sequences are considered invalid. Peculiar cases
            // in ASCII include control codes (other than whitespace), and  backslashes (\)
            // which are not immediately followed by 'u'. Non-ASCII cases include usage of
            // characters outside of identifier character set (e.g., general categories like
            // No, Sk, or C), or usage of bare identifier continuation characters (without
            // a starter character preceding them). The whole hunk of such invalid characters
            // is reported as Unrecognized.
            ("\u{00}\u{03}\u{04}\u{05}\u{06}\u{07}\u{08}"   => Unrecognized),
            (" "                                            => Whitespace),
            ("\u{12}\u{1A}\u{1B}\u{1C}"                     => Unrecognized),
            (" "                                            => Whitespace),
            ("\u{1D}\u{1E}\u{1F}\u{7F}\u{80}\u{81}"         => Unrecognized),
            (" "                                            => Whitespace),
            ("\u{82}\u{83}\u{84}"                           => Unrecognized),
            (" "                                            => Whitespace),
            ("\u{e123}\u{F700}\u{FF000}\u{100000}"          => Unrecognized),
            (" "                                            => Whitespace),
            ("\u{200B}\u{180E}\u{2062}\u{E0001}\u{E007F}"   => Unrecognized),
            (" "                                            => Whitespace),
            ("\\"                                           => Unrecognized),
            ("x12"                                          => Identifier("x12")),
            (" "                                            => Whitespace),
            ("\\\\"                                         => Unrecognized),
            (" "                                            => Whitespace),
            ("test\\"                                       => Identifier("test\\")),
            (" "                                            => Whitespace),
            ("\u{0307}\u{09E3}\\\u{1DA61}\u{200D}"          => Unrecognized),
            ("1"                                            => Literal(Integer, "1")),
            ("\u{200C}\u{7F}\u{200D}"                       => Unrecognized),
            ("x\u{200D}y"                                   => Identifier("x\u{200D}y")),
            ("\n"                                           => Whitespace),
            // However! The scanner tolerates invalid Unicode characters in the middle of
            // identifiers. They are still reported, but the scanning goes on afterwards
            // as if they were valid, including their usage for boundary detection.
            ("f\u{0}o"                                      => Identifier("f\u{0}o")),
            ("+\u{E666}"                                    => Identifier("+\u{E666}")),
            ("_\u{10}some\u{11}_\\invalid\\123"             => Identifier("_\u{10}some\u{11}_\\invalid\\123")),
            ("==\u{02DC}=="                                 => Identifier("==\u{02DC}==")),
            (" "                                            => Whitespace),
            ("a\u{0488}b"                                   => Identifier("a\u{0488}b")),
            (" "                                            => Whitespace),
            ("C\u{20DD}_\u{20E3}"                           => Identifier("C\u{20DD}_\u{20E3}")),
            (" "                                            => Whitespace),
            ("+\u{200D}+=\u{200D}"                          => Identifier("+\u{200D}+=\u{200D}"));

        Severity::Error:
            (  0,   7), (  8,  12), ( 13,  21), ( 22,  28), ( 29,  43), ( 44,  61), ( 62,  63),
            ( 67,  69), ( 74,  75), ( 76,  89), ( 90,  97), (104, 105), (107, 110), (111, 112),
            (116, 117), (118, 119), (126, 127), (132, 134), (138, 140), (143, 146), (147, 150),
            (152, 155), (157, 160);
        }
    }

    #[test]
    fn identifier_invalid_characters_escaped() {
        check! {
            // The scanner also tolerates (i.e., is able to recover from) invalid escaped Unicode
            // characters in the middle of identifiers. This also includes surrogates (which can't
            // be embedded into Rust strings as is), and other invalid escapes.
            (r"f\u{2000}o"                                  => Identifier("f\u{2000}o")),
            (r"+\u{E666}"                                   => Identifier("+\u{E666}")),
            (r"_\u{60}some\u{7F}_\invalid\123"              => Identifier("_\u{FFFD}some\u{FFFD}_\\invalid\\123")),
            (r"==\u{02DC}=="                                => Identifier("==\u{02DC}==")),
            (r" "                                           => Whitespace),
            (r"a\u{0488}b"                                  => Identifier("a\u{0488}b")),
            (r" "                                           => Whitespace),
            (r"C\u{20DD}_\u{20E3}"                          => Identifier("C\u{20DD}_\u{20E3}")),
            (r" "                                           => Whitespace),
            (r"+\u{200D}+=\u{200D}"                         => Identifier("+\u{200D}+=\u{200D}")),
            (r" "                                           => Whitespace),
            (r"f\u{}o"                                      => Identifier("f\u{FFFD}o")),
            (r" "                                           => Whitespace),
            (r"f\u{REPLACEMENT CHARACTER}o"                 => Identifier("f\u{FFFD}o")),
            (r"+\uD900\uDDDD"                               => Identifier("+\u{FFFD}\u{FFFD}")),
            (r"_\u{9999999999999999}_"                      => Identifier("_\u{FFFD}_"));

        Severity::Error:
            (  1,   9), ( 11,  19), ( 20,  26), ( 30,  36), ( 37,  38), ( 45,  46), ( 51,  59),
            ( 63,  71), ( 74,  82), ( 83,  91), ( 93, 101), (103, 111), (115, 117), (120, 145),
            (149, 153), (147, 153), (155, 159), (153, 159), (160, 180);
        }
    }

    #[test]
    fn identifier_unicode_ascii_escapes() {
        check! {
            (r"f\u{6F}o"                                    => Identifier("f\u{FFFD}o")),
            (r" "                                           => Whitespace),
            (r"example\u{2E}com"                            => Identifier("example\u{FFFD}com")),
            (r" "                                           => Whitespace),
            (r"\u{2E}\u{2E}\u{2E}"                          => Unrecognized),
            (r" "                                           => Whitespace),
            (r"\u{2E}"                                      => Unrecognized),
            (r"."                                           => Dot),
            (r"\u{2E}"                                      => Unrecognized),
            (r" "                                           => Whitespace),
            (r"c\u{31}2"                                    => Identifier("c\u{FFFD}2")),
            (r" "                                           => Whitespace),
            (r"test\u{0020}test"                            => Identifier("test\u{FFFD}test")),
            (r" "                                           => Whitespace),
            (r"a\u{2B}b"                                    => Identifier("a\u{FFFD}b")),
            (r" "                                           => Whitespace),
            (r"*\u{3E}*"                                    => Identifier("*\u{FFFD}*")),
            (r" "                                           => Whitespace),
            ("\u{2045}\\u{60}"                              => Identifier("\u{2045}\u{FFFD}"));

        Severity::Error:
            (  1,   7), ( 16,  22), ( 26,  44), ( 45,  51), ( 52,  58), ( 60,  66), ( 72,  80),
            ( 86,  92), ( 95, 101), (106, 112);
        }
    }

    #[test]
    fn identifier_invalid_quote_modifiers() {
        check! {
            // One peculiar case is usage of modifier characters after quote identifiers.
            // Instead of being reported as a separate Unrecognized token they are included
            // into the quote token (after getting reported, of course).
            ("\u{2045}\u{0488}"                             => Identifier("\u{2045}\u{0488}")),
            ("\u{276E}\u{0DDC}\u{16F7A}"                    => Identifier("\u{276E}\u{0DDC}\u{16F7A}")),
            ("\u{0F3D}\u{200D}\u{20DD}"                     => Identifier("\u{0F3D}\u{200D}\u{20DD}")),
            ("\u{FE18}\u{093F}\u{0A3F}"                     => Identifier("\u{FE18}\u{093F}\u{0A3F}")),
            ("\u{00AB}\u{0324}\u{0483}"                     => Identifier("\u{00AB}\u{0324}\u{0483}")),
            ("\u{2039}\u{0CC7}"                             => Identifier("\u{2039}\u{0CC7}")),
            ("\u{2019}\u{20E2}"                             => Identifier("\u{2019}\u{20E2}")),
            ("\u{2E0A}\u{17CA}\u{200C}\u{1B3C}"             => Identifier("\u{2E0A}\u{17CA}\u{200C}\u{1B3C}"));
        Severity::Error:
            ( 3,  5), ( 8, 11), (11, 15), (18, 21), (21, 24), (27, 30), (30, 33), (35, 37),
            (37, 39), (42, 45), (48, 51), (54, 57), (57, 60), (60, 63);
        }
    }

    #[test]
    fn identifier_special_raw_strings() {
        check! {
            // Raw strings start with an 'r' which is a valid starter of word identifiers.
            // We must not confuse them.
            ("r\"awr\""         => Literal(RawString, "awr")),
            (" "                => Whitespace),
            ("ra"               => Identifier("ra")),
            ("\"wr\""           => Literal(String, "wr")),
            (" "                => Whitespace),
            ("raaaaa"           => Identifier("raaaaa")),
            ("#"                => Hash),
            ("#"                => Hash),
            ("\"wr\""           => Literal(String, "wr")),
            ("#"                => Hash),
            ("#"                => Hash),
            (" "                => Whitespace),
            ("r#\"awr\"#"       => Literal(RawString, "awr"));
        }
    }

    // TODO: boundary tests between all token types

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Symbols

    #[test]
    fn symbol_implicit() {
        check! {
            // Implicit symbols are word identifiers followed by a single literal colon.
            // For example, ASCII words are fine:
            ("foo:"                                         => ImplicitSymbol("foo")),
            (" "                                            => Whitespace),
            ("Symbol:"                                      => ImplicitSymbol("Symbol")),
            (" "                                            => Whitespace),
            ("_:"                                           => ImplicitSymbol("_")),
            (" "                                            => Whitespace),
            ("_1:"                                          => ImplicitSymbol("_1")),
            (" "                                            => Whitespace),
            // Unicode words are fine too:
            ("\u{691C}\u{67FB}:"                            => ImplicitSymbol("\u{691C}\u{67FB}")),
            (" "                                            => Whitespace),
            ("\u{1FAA}:"                                    => ImplicitSymbol("\u{1FAA}")),
            (" "                                            => Whitespace),
            ("\u{3007}\u{3007}\u{3007}:"                    => ImplicitSymbol("\u{3007}\u{3007}\u{3007}")),
            (" "                                            => Whitespace),
            ("\u{212E}\u{2118}:"                            => ImplicitSymbol("\u{212E}\u{2118}")),
            (" "                                            => Whitespace),
            ("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}:"    => ImplicitSymbol("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}")),
            (" "                                            => Whitespace),
            // As well as escaped ones:
            ("\u{005F}\\u{0661}\\u{0665}:"                  => ImplicitSymbol("\u{005F}\u{0661}\u{0665}")),
            (" "                                            => Whitespace),
            ("\u{005F}\\u{FE4F}\u{005F}:"                   => ImplicitSymbol("\u{005F}\u{FE4F}\u{005F}")),
            (" "                                            => Whitespace),
            ("\u{0078}\\u{19DA}:"                           => ImplicitSymbol("\u{0078}\u{19DA}")),
            (" "                                            => Whitespace),
            ("\\u{0915}\u{094D}\\u{0937}:"                  => ImplicitSymbol("\u{0915}\u{094D}\u{0937}")),
            (" "                                            => Whitespace),
            ("\\u{1FAA}:"                                   => ImplicitSymbol("\u{1FAA}")),
            (" "                                            => Whitespace);
        }
    }

    #[test]
    fn symbol_implicit_boundaries() {
        check! {
            // Only a single colon forms a boundary for a symbol. It can be followed by anything
            // except for another colon, in which case we see a word identifier followed by
            // a double colon.
            ("foo:"                                 => ImplicitSymbol("foo")),
            ("+"                                    => Identifier("+")),
            ("bar"                                  => Identifier("bar")),
            (" "                                    => Whitespace),
            ("x:"                                   => ImplicitSymbol("x")),
            ("\n"                                   => Whitespace),
            ("y:"                                   => ImplicitSymbol("y")),
            (" "                                    => Whitespace),
            ("z:"                                   => ImplicitSymbol("z")),
            ("':'"                                  => Literal(Character, ":")),
            (" "                                    => Whitespace),
            ("_:"                                   => ImplicitSymbol("_")),
            ("10"                                   => Literal(Integer, "10")),
            (" "                                    => Whitespace),
            ("zork"                                 => Identifier("zork")),
            ("::"                                   => Dualcolon),
            ("x"                                    => Identifier("x")),
            (" "                                    => Whitespace),
            // Also, only word identifiers can be implicit symbols
            ("++"                                   => Identifier("++")),
            (":"                                    => Colon),
            ("$"                                    => Identifier("$")),
            (":"                                    => Colon),
            (";"                                    => Semicolon),
            (":"                                    => Colon),
            ("["                                    => OpenDelim(Bracket)),
            (":"                                    => Colon),
            ("]"                                    => CloseDelim(Bracket)),
            ("\u{2025}"                             => Identifier("\u{2025}")),
            (":"                                    => Colon),
            (" "                                    => Whitespace),
            ("\u{0024}\u{0488}"                     => Identifier("\u{0024}\u{0488}")),
            (":"                                    => Colon),
            ("\u{FE18}"                             => Identifier("\u{FE18}")),
            (":"                                    => Colon),
            ("\u{300E}"                             => Identifier("\u{300E}")),
            // This includes escaped identifiers
            ("\u{220F}\\u{2230}"                    => Identifier("\u{220F}\u{2230}")),
            (":"                                    => Colon),
            ("\u{19FB}\u{19FF}"                     => Identifier("\u{19FB}\u{19FF}")),
            (":"                                    => Colon),
            (" "                                    => Whitespace),
            ("\\u{26B5}\\u{1D1E7}"                  => Identifier("\u{26B5}\u{1D1E7}")),
            ("::"                                   => Dualcolon),
            ("\\u{2E02}"                            => Identifier("\u{2E02}")),
            (":"                                    => Colon),
            (" "                                    => Whitespace),
            ("\\u{2E21}"                            => Identifier("\u{2E21}")),
            (" "                                    => Whitespace),
            // Finally, implicit symbols do not allow type suffixes
            ("foo:"                                 => ImplicitSymbol("foo")),
            ("bar"                                  => Identifier("bar")),
            ("::"                                   => Dualcolon),
            ("baz:"                                 => ImplicitSymbol("baz")),
            ("_"                                    => Identifier("_")),
            (" "                                    => Whitespace),
            // And cannot 'steal' others' suffixes
            ("123foo"                               => Literal(Integer, "123", "foo")),
            (":"                                    => Colon),
            ("bar:"                                 => ImplicitSymbol("bar")),
            (" "                                    => Whitespace),
            ("'x'x"                                 => Literal(Character, "x", "x")),
            ("::"                                   => Dualcolon),
            ("y"                                    => Identifier("y"));
        }
    }

    #[test]
    fn symbol_implicit_invalid_characters() {
        check! {
            // Invalid Unicode escapes and characters in symbols are reported as usual
            ("a\\u{0488}b:"                                 => ImplicitSymbol("a\u{0488}b")),
            (" "                                            => Whitespace),
            ("a\u{0488}b:"                                  => ImplicitSymbol("a\u{0488}b")),
            (" "                                            => Whitespace),
            ("example\\u{2E}com:"                           => ImplicitSymbol("example\u{FFFD}com")),
            (" "                                            => Whitespace),
            ("f\\u{REPLACEMENT CHARACTER}o:"                => ImplicitSymbol("f\u{FFFD}o")),
            (" "                                            => Whitespace),
            ("w\\u2113\\u1d466d:"                           => ImplicitSymbol("w\u{2113}\u{FFFD}")),
            (" "                                            => Whitespace),
            ("C\u{20DD}_\u{20E3}:"                          => ImplicitSymbol("C\u{20DD}_\u{20E3}")),
            (" "                                            => Whitespace),
            ("test\\u{003A}:"                               => ImplicitSymbol("test\u{FFFD}"));

        Severity::Error:
            (  1,   9), ( 13,  15), ( 25,  31), ( 37,  62), ( 68,  72), ( 74,  80), ( 72,  80),
            ( 83,  86), ( 87,  90), ( 96, 104);
        }
    }

    #[test]
    fn symbol_explicit() {
        check! {
            // Explicit symbols look like strings quoted with backquote,
            ("`foo`"                                        => ExplicitSymbol("foo")),
            (" "                                            => Whitespace),
            ("`one two three`"                              => ExplicitSymbol("one two three")),
            ("`1-2-3`"                                      => ExplicitSymbol("1-2-3")),
            (" "                                            => Whitespace),
            ("`'\"'`"                                       => ExplicitSymbol("'\"'")),
            (" "                                            => Whitespace),
            ("``"                                           => ExplicitSymbol("")),
            (" "                                            => Whitespace),
            // They can contain Unicode and support all character escape sequences,
            // plus an additional escape sequence for the backquote character
            ("`\\0\\t\\r\\n\\\\\\\"`"                       => ExplicitSymbol("\0\t\r\n\\\"")),
            (" "                                            => Whitespace),
            ("`\u{3053}\u{3093}\u{306B}\u{3061}\u{306F}`"   => ExplicitSymbol("\u{3053}\u{3093}\u{306B}\u{3061}\u{306F}")),
            (" "                                            => Whitespace),
            ("`\\u{05E9}\\u{05DC}\\u{05D5}\\u{05DD}`"       => ExplicitSymbol("\u{05E9}\u{05DC}\u{05D5}\u{05DD}")),
            (" "                                            => Whitespace),
            ("`\x00\x32`"                                   => ExplicitSymbol("\x00\x32")),
            (" "                                            => Whitespace),
            ("`///*//*/`"                                   => ExplicitSymbol("///*//*/")),
            (" "                                            => Whitespace),
            ("`\\`...\\``"                                  => ExplicitSymbol("`...`"));
        }
    }

    #[test]
    fn symbol_explicit_invalid_escapes() {
        check! {
            // Invalid escape sequences in explicit symbols are reported as in string literal
            (r"`\u{123\u456}\u{testing...}`"                => ExplicitSymbol("\u{123}\u{456}\u{FFFD}")),
            (r" "                                           => Whitespace),
            (r"`\uguu\uDEAD\uF0F0F0F0F0F0F0F0\u`"           => ExplicitSymbol("\u{FFFD}guu\u{FFFD}\u{FFFD}\u{FFFD}")),
            (r" "                                           => Whitespace),
            (r"`\a\b\f\v\?\'`"                              => ExplicitSymbol("abfv?'")),
            (r" "                                           => Whitespace),
            (r"`\x\x1\x1234`"                               => ExplicitSymbol("\u{FFFD}\u{FFFD}\u{FFFD}"));

        Severity::Error:
            ( 7,  7), ( 9,  9), (13, 27), (32, 32), (37, 41), (35, 41), (43, 59), (41, 59),
            (61, 61), (64, 66), (66, 68), (68, 70), (70, 72), (72, 74), (74, 76), (79, 81),
            (81, 84), (84, 90);
        }
    }

    #[test]
    fn symbol_explicit_invalid_mulitline() {
        check! {
            // Explicit symbols cannot span multiple lines. They are handled similar to character
            // literals. Though, one can embed newline characters into them via escape sequences.
            ("`example"                                     => Unrecognized),
            ("\n"                                           => Whitespace),
            ("`some more"                                   => Unrecognized),
            ("\r\n"                                         => Whitespace),
            ("`Old\rApple`"                                 => ExplicitSymbol("Old\rApple")),
            ("`"                                            => Unrecognized),
            ("\n"                                           => Whitespace),
            ("`"                                            => Unrecognized),
            ("\r\n"                                         => Whitespace),
            ("`\r`"                                         => ExplicitSymbol("\r")),
            ("\n"                                           => Whitespace),
            ("`\\"                                          => Unrecognized),
            ("\n\t"                                         => Whitespace),
            ("`\\"                                          => Unrecognized),
            ("\r\n"                                         => Whitespace),
            ("`\\\r`"                                       => ExplicitSymbol("\r")),
            ("\t"                                           => Whitespace),
            ("test"                                         => Identifier("test")),
            ("`"                                            => Unrecognized);

        Severity::Error:
            (25, 26), (38, 39), (51, 52), (50, 52);

        Severity::Fatal:
            ( 0,  8), ( 9, 19), (32, 33), (34, 35), (41, 43), (45, 47), (58, 59);
        }
    }

    #[test]
    fn symbol_explicit_premature_termination() {
        // Unexpected EOFs are handled similar to characters and strings
        check! { ("`"      => Unrecognized); Severity::Fatal: (0, 1); }
        check! { ("`xyz"   => Unrecognized); Severity::Fatal: (0, 4); }
        check! { ("`\\x"   => Unrecognized); Severity::Error: (1, 3);
                                             Severity::Fatal: (0, 3); }
        check! { ("`\\u"   => Unrecognized); Severity::Error: (3, 3);
                                             Severity::Fatal: (0, 3); }
        check! { ("`\\u{1" => Unrecognized); Severity::Error: (5, 5);
                                             Severity::Fatal: (0, 5); }
    }

    #[test]
    fn symbol_explicit_no_type_suffixes() {
        check! {
            // Explicit symbols do not have type suffixes. They are terminated right after the
            // backquote.
            ("`foo`"        => ExplicitSymbol("foo")),
            ("bar"          => Identifier("bar")),
            ("`baz`"        => ExplicitSymbol("baz")),
            (" "            => Whitespace),
            ("`o`"          => ExplicitSymbol("o")),
            ("r\"a\""       => Literal(RawString, "a")),
            (" "            => Whitespace),
            ("`x`"          => ExplicitSymbol("x")),
            ("'y'"          => Literal(Character, "y")),
            ("\"z\""        => Literal(String, "z")),
            (" "            => Whitespace),
            ("``"           => ExplicitSymbol("")),
            ("+"            => Identifier("+")),
            ("``"           => ExplicitSymbol("")),
            (" "            => Whitespace),
            ("`.`"          => ExplicitSymbol(".")),
            ("."            => Dot),
            ("`.`"          => ExplicitSymbol(".")),
            (" "            => Whitespace),
            ("`:`"          => ExplicitSymbol(":")),
            (":"            => Colon),
            ("e"            => Identifier("e"));
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Test helpers

    use std::cell::RefCell;
    use std::rc::Rc;

    struct ScannerTestSlice<'a>(&'a str, Token);

    struct ScannerTestResults {
        pub tokens: Vec<ScannedToken>,
        pub fatals: Vec<Span>,
        pub errors: Vec<Span>,
    }

    struct SinkReporter {
        pub diagnostics: Rc<RefCell<Vec<(Severity, Span)>>>,
    }

    impl diagnostics::Reporter for SinkReporter {
        fn report(&mut self, severity: Severity, _: &str, loc: Option<Span>) {
            let mut diagnostics = self.diagnostics.borrow_mut();

            // Scanner diagnostics always come with a location.
            diagnostics.push((severity, loc.unwrap()));
        }
    }

    impl SinkReporter {
        fn new(diagnostics: Rc<RefCell<Vec<(Severity, Span)>>>) -> SinkReporter {
            SinkReporter {
                diagnostics: diagnostics,
            }
        }
    }

    /// Checks whether a sequence of test string slices yields consistent results and generates
    /// expected diagnostics.
    fn check(slices: &[ScannerTestSlice], diagnostics: &[(Severity, Span)], pool: InternPool) {
        let (test_string, expected) = preprocess_expected_data(slices, diagnostics);

        let actual = process_test_string(&test_string, &pool);

        let token_failures =
            verify("Tokens", &expected.tokens, &actual.tokens,
                |tok| print_token(tok, &test_string, &pool));

        let fatal_failures =
            verify("Fatal errors", &expected.fatals, &actual.fatals,
                |span| print_span(span, &test_string));

        let error_failures =
            verify("Errors", &expected.errors, &actual.errors,
                |span| print_span(span, &test_string));

        if let Some(first_failure) = token_failures {
            panic!("first invalid token: #{}", first_failure);
        }

        if let Some(first_failure) = fatal_failures {
            panic!("first invalid fatal: #{}", first_failure);
        }

        if let Some(first_failure) = error_failures {
            panic!("first invalid error: #{}", first_failure);
        }
    }

    /// Reorder and rearrange raw test data into the input string and expected results.
    fn preprocess_expected_data(slices: &[ScannerTestSlice], diagnostics: &[(Severity, Span)])
        -> (String, ScannerTestResults)
    {
        let (test_string, tokens) = expand_test_slices(slices);
        let (fatals, errors) = partition_diagnostics(diagnostics);

        (test_string, ScannerTestResults {
            tokens: tokens,
            fatals: fatals,
            errors: errors,
        })
    }

    /// Preprocesses test slices, returning the whole string to be scanned over
    /// and the list of expected tokens with their respective spans.
    fn expand_test_slices(slices: &[ScannerTestSlice]) -> (String, Vec<ScannedToken>) {
        let mut all_str = String::new();
        let mut all_tok = Vec::new();

        let mut bytes = 0;
        for &ScannerTestSlice(s, ref t) in slices {
            all_str.push_str(s);
            all_tok.push(ScannedToken {
                tok: t.clone(),
                span: Span::new(bytes, bytes + s.len())
            });
            bytes += s.len();
        }

        all_tok.push(ScannedToken { tok: Token::EOF, span: Span::new(bytes, bytes) });

        return (all_str, all_tok);
    }

    /// Performs actual scanning of the `whole_string`, producing a list of resulting tokens
    /// and a number of diagnostics which were emitted during scanning.
    fn process_test_string(whole_string: &str, pool: &InternPool) -> ScannerTestResults {
        let mut tokens = Vec::new();
        let diagnostics = Rc::new(RefCell::new(Vec::new()));
        let reporter = SinkReporter::new(diagnostics.clone());
        let handler = SpanReporter::with_reporter(Box::new(reporter));

        let mut scanner = StringScanner::new(whole_string, pool, &handler);

        // Loop with postcondition to catch the EOF token
        loop {
            let token = scanner.next_token();

            tokens.push(token.clone());

            if token.tok == Token::EOF {
                break;
            }
        }

        assert!(scanner.at_eof());

        let (fatals, errors) = partition_diagnostics(&diagnostics.borrow()[..]);

        return ScannerTestResults {
            tokens: tokens,
            fatals: fatals,
            errors: errors,
        };
    }

    /// Partitions diagnostics by severity.
    fn partition_diagnostics(diagnostics: &[(Severity, Span)]) -> (Vec<Span>, Vec<Span>) {
        use std::cmp;

        let mut fatals = Vec::new();
        let mut errors = Vec::new();

        for &(severity, span) in diagnostics {
            match severity {
                Severity::Fatal => fatals.push(span),
                Severity::Error => errors.push(span),
            }
        }

        fn span_position(lhs: &Span, rhs: &Span) -> cmp::Ordering {
            if lhs.from < rhs.from {
                return cmp::Ordering::Less;
            }
            if lhs.from > rhs.from {
                return cmp::Ordering::Greater;
            }
            return lhs.to.cmp(&rhs.to);
        }

        fatals.sort_by(span_position);
        errors.sort_by(span_position);

        return (fatals, errors);
    }

    /// Prints out and verifies produced results. Returns Some 1-based index of the first incorrect
    /// item, or None if the actual results are equal to expected ones.
    fn verify<T, F>(title: &str, expected: &[T], actual: &[T], to_string: F) -> Option<u32>
        where T: Eq, F: Fn(&T) -> String
    {
        if expected.is_empty() && actual.is_empty() {
            return None;
        }

        print!("\n{}\n\nindex:\n\t<expected>\n\t<actual>\n", title);

        let mut first_mismatch = None;

        for (index, (expected, actual)) in (1..).zip(longest_zip(expected, actual)) {
            let bad = actual != expected;

            if bad && first_mismatch.is_none() {
                first_mismatch = Some(index);
            }

            print!("{index}:\n{ind_ex}\t{expected}\n{ind_act}\t{actual}\n",
                index     = index,
                ind_ex    = if bad { "-- exp:" } else { "" },
                ind_act   = if bad { "-- act:" } else { "" },
                expected  = expected.map_or("None".to_string(), &to_string),
                actual    = actual.  map_or("None".to_string(), &to_string),
            );
        }

        return first_mismatch;
    }

    fn print_token(token: &ScannedToken, buf: &str, pool: &InternPool) -> String {
        format!("{token} @ [{from}, {to}] = {slice:?}",
            token = pretty_print_token(&token.tok, pool),
            from  = token.span.from,
            to    = token.span.to,
            slice = &buf[token.span.from..token.span.to],
        )
    }

    fn print_span(span: &Span, buf: &str) -> String {
        format!("[{from}, {to}] = {slice:?}",
            from  = span.from,
            to    = span.to,
            slice = &buf[span.from..span.to],
        )
    }

    fn pretty_print_token(token: &Token, pool: &InternPool) -> String {
        match *token {
            Token::DocComment(_) => "DocComment".to_string(),

            Token::Identifier(atom)     => format!("Identifier({:?})",     pool.get(atom)),
            Token::ImplicitSymbol(atom) => format!("ImplicitSymbol({:?})", pool.get(atom)),
            Token::ExplicitSymbol(atom) => format!("ExplicitSymbol({:?})", pool.get(atom)),

            Token::Literal(ref lit, ref suffix) => pretty_print_literal(lit, suffix, pool),

            _ => format!("{:?}", token)
        }
    }

    fn pretty_print_literal(lit: &Lit, suffix: &Option<Atom>, pool: &InternPool) -> String {
        let expr = match *lit {
            Lit::Integer(atom)   => format!("Integer({:?})",   pool.get(atom)),
            Lit::Float(atom)     => format!("Float({:?})",     pool.get(atom)),
            Lit::Character(atom) => format!("Character({:?})", pool.get(atom)),
            Lit::String(atom)    => format!("String({:?})",    pool.get(atom)),
            Lit::RawString(atom) => format!("RawString({:?})", pool.get(atom)),
        };

        if let &Some(atom) = suffix {
            format!("Literal({}, '{}')", expr, pool.get(atom))
        } else {
            format!("Literal({})", expr)
        }
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Test utilities

    struct LongestZip<A, B> {
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
    fn longest_zip<A, B>(iter1: A, iter2: B) -> LongestZip<A::IntoIter, B::IntoIter>
        where A: IntoIterator, B: IntoIterator
    {
        LongestZip { a: iter1.into_iter(), b: iter2.into_iter() }
    }
}
