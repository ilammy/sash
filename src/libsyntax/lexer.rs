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

use tokens::{Token, Delimiter, Keyword, Lit};
use diagnostics::{Span, Handler};
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
    /// If it is reached, the scanner will produce only `Token::Eof`.
    fn at_eof(&self) -> bool;

    /// Extracts and returns the next token from the stream. Returns `Token::Eof`
    /// if the end of stream has been reached and no more tokens are available.
    fn next_token(&mut self) -> ScannedToken;
}

/// A scanner for strings.
pub struct StringScanner<'a> {
    /// The string being scanned.
    buf: &'a str,

    /// The intern pool for atoms stored in scanned tokens.
    pool: &'a InternPool,

    // Cached keyword atoms.
    atoms: AtomCache,

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
    // Diagnostic reporting
    //

    /// Our designated responsible for diagnostic processing.
    report: &'a Handler,
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
    /// to the given handler and intern strings into the given pool.
    pub fn new(s: &'a str, pool: &'a InternPool, handler: &'a Handler) -> StringScanner<'a> {
        let mut scanner = StringScanner {
            buf: s,
            pool: pool,
            atoms: AtomCache::new(pool),
            cur: None, pos: 0, prev_pos: 0,
            report: handler,
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
                tok: Token::Eof,
                span: Span::new(self.pos, self.pos)
            };
        }

        let start = self.prev_pos;
        let tok = self.scan_token();
        let end = self.prev_pos;

        assert!(tok != Token::Eof);

        return ScannedToken {
            tok: tok,
            span: Span::new(start, end)
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
        let comment_start = self.prev_pos;

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

        let comment_end = self.prev_pos;

        return if doc_comment {
            Token::DocComment(self.intern_slice(comment_start, comment_end))
        } else { Token::Comment };
    }

    /// Scan a block comment.
    fn scan_block_comment(&mut self) -> Token {
        let comment_start = self.prev_pos;

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

        let comment_end = self.prev_pos;

        if nesting_level > 0 {
            if doc_comment {
                self.report.fatal(Span::new(comment_start, comment_end),
                    "unterminated block comment, expected '*/'");
            } else {
                self.report.fatal(Span::new(comment_start, comment_end),
                    "unterminated documentation comment, expected '*/'");
            }

            return Token::Unrecognized;
        }

        return if doc_comment {
            Token::DocComment(self.intern_slice(comment_start, comment_end))
        } else { Token::Comment };
    }

    /// Scan over any number literal.
    fn scan_number(&mut self) -> Token {
        let number_start = self.prev_pos;

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
            self.report.error(Span::new(number_start, self.prev_pos),
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
                let literal = self.intern_slice(number_start, self.prev_pos);
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

        let number_end = self.prev_pos;

        // Some late check for floating-point base. We do not support binary literals for floats.
        if !integer && (base != 10) {
            self.report.error(Span::new(number_start, number_end),
                "only decimal base is supported for floating-point numbers");
        }

        let literal = self.intern_slice(number_start, number_end);

        let suffix = self.scan_optional_type_suffix();

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

        let char_start = self.prev_pos;

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
                                    self.report.error(Span::new(char_start, self.prev_pos),
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
                    self.report.error(Span::new(char_start, self.prev_pos),
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
                self.report.fatal(Span::new(char_start, self.prev_pos),
                    "unterminated character constant, expected a closing single quote (')");

                return Token::Unrecognized;
            }
        }
    }

    /// Scan over a string literal.
    fn scan_string(&mut self) -> Token {
        use self::StringSpecials::{DoubleQuote, SkippedEscapedLineEnding, UnexpectedTerminator};

        let string_start = self.prev_pos;

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
                    self.report.fatal(Span::new(string_start, self.prev_pos),
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

        let symbol_start = self.prev_pos;

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
                    self.report.fatal(Span::new(symbol_start, self.prev_pos),
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
                self.read();
                self.read();
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
        let string_start = self.prev_pos - (hash_count as usize) - 1; // unwind leading `r#...#`

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
                    self.report.fatal(Span::new(string_start, self.prev_pos),
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

        let identifier_start = self.prev_pos;

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
                return self.scan_unrecognized(identifier_start);
            }
            // Ignore invalid Unicode escapes as well
            Err(IncorrectUnicodeEscape) | Err(AsciiUnicodeEscape) => {
                return self.scan_unrecognized(identifier_start);
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
    fn scan_unrecognized(&mut self, mayhem_start: usize) -> Token {
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

        self.report.error(Span::new(mayhem_start, self.prev_pos),
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

        return Token::Identifier(self.intern_string(normalize_identifer(&value)));
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

        // Some word identifiers are reserved as keywords.
        match initial_token {
            Token::Identifier(atom) => {
                if atom == self.atoms.module { return Token::Keyword(Keyword::Module) }
                if atom == self.atoms.library { return Token::Keyword(Keyword::Library) }
            }
            _ => unreachable!()
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

        return Token::Identifier(self.intern_string(normalize_identifer(&value)));
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

        return Token::Identifier(self.intern_string(normalize_identifer(&value)));
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

/// Sash keyword strings.
///
/// These are used to discern keywords from identifiers. We cache them beforehand to avoid
/// reinterning strings with each scanned identifier. The atom values refer to the intern pool
/// used by the scanner. Also note that these are public fields and it is obviously a bad idea
/// to modify them after the cache is created.
struct AtomCache {
    pub library: Atom,
    pub module: Atom,
}

impl AtomCache {
    /// Make a new atom cache from the given pool.
    pub fn new(pool: &InternPool) -> AtomCache {
        AtomCache {
            library: pool.intern("library"),
            module: pool.intern("module"),
        }
    }
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

/// Normalizes identifier spelling.
fn normalize_identifer(ident: &str) -> String {
    use unicode::normalization;

    // All identifiers pass though NFKC normalization to fold visual ambiguities and unify binary
    // representations of visually identical strings so that they are considered equal.
    let normalized = normalization::nfkc(ident);

    // In addition to that we also remove zero-width (non) joiner characters which are allowed
    // in word identifiers. They also may create ambiguity when inserted between non-joinable
    // characters. Thus we allow their usage in identifiers, but ignore them during comparison.
    const ZWNJ: char = '\u{200C}';
    const ZWJ: char = '\u{200D}';
    let cleaned = normalized.chars().filter(|&c| !(c == ZWJ || c == ZWNJ)).collect();

    return cleaned;
}
