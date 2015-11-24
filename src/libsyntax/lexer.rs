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

use tokens::{Token};
use diagnostics::{Span, SpanReporter};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// Helper data structures
//

/// A scanned token with extents information.
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
pub trait Scanner<'a> {
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
    report: &'a SpanReporter<'a>,
}

impl<'a> Scanner<'a> for StringScanner<'a> {
    fn at_eof(&self) -> bool {
        self.cur.is_none()
    }

    fn next_token(&mut self) -> ScannedToken {
        self.next()
    }
}

impl<'a> StringScanner<'a> {
    /// Makes a new scanner for the given string which will report scanning errors
    /// to the given reporter.
    pub fn new<'b>(s: &'b str, reporter: &'b SpanReporter<'b>) -> StringScanner<'b> {
        let mut scanner = StringScanner {
            buf: s,
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
            '(' => { self.read(); Token::Lparen }
            ')' => { self.read(); Token::Rparen }
            '[' => { self.read(); Token::Lbrack }
            ']' => { self.read(); Token::Rbrack }
            '{' => { self.read(); Token::Lbrace }
            '}' => { self.read(); Token::Rbrace }
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
                    self.read();
                    break;
                }
                '\r' if self.peek_is('\n') => {
                    self.read();
                    self.read();
                    break;
                }
                // Report bare CR characters as they may have meant to be line endings,
                // but are not treated as such in Sash.
                '\r' => {
                    if doc_comment {
                        self.report.error(Span::new(self.prev_pos, self.pos),
                            "Bare CR characters are not allowed in documentation \
                             comments");
                    } else {
                        self.report.warning(Span::new(self.prev_pos, self.pos),
                            "Bare CR character encountered in a line comment. \
                             Did you mean Windows line ending, CRLF?");
                    }
                    self.read();
                }
                // Skip over anything else, we're scanning a comment
                _ => { self.read(); }
            }
        }

        return if doc_comment { Token::DocComment } else { Token::Comment };
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
                        "Bare CR characters are not allowed in documentation \
                         comments");
                    self.read();
                }
                // Skip over anything else, we're scanning a comment
                _ => { self.read(); }
            }
        }

        if nesting_level > 0 {
            if doc_comment {
                self.report.error(Span::new(self.start, self.pos),
                    "Unexpected end of file while reading a documentation comment. \
                     Please look for the missing block comment closure */");
            } else {
                self.report.error(Span::new(self.start, self.pos),
                    "Unexpected end of file while reading a block comment. \
                     Please look for the missing block comment closure */");
            }

            return Token::Unrecognized;
        }

        return if doc_comment { Token::DocComment } else { Token::Comment };
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

        // The integer part may contain no valid digits, like in "0o999" or "0x__"
        if digits == 0 {
            self.report.error(Span::new(self.start, self.prev_pos),
                "The number contains no valid digits");
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
                return Token::Integer;
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

        self.scan_optional_type_suffix();

        // Some late check for floating-point base. We do not support binary literals for floats.
        if !integer && (base != 10) {
            self.report.error(Span::new(self.start, self.prev_pos),
                "Float number must be decimal");
        }

        return if integer { Token::Integer } else { Token::Float };
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

    /// Scan over a fractional part of a floating-point literal.
    fn scan_float_fractional_part(&mut self) {
        assert!(is_digit(self.cur.unwrap(), 10) || self.cur_is('_'));

        let fractional_start = self.prev_pos;
        let fractional_digits = self.scan_digits(10, 10);

        if fractional_digits == 0 {
            self.report.error(Span::new(fractional_start, self.prev_pos),
                "The fractional part contains no valid digits");
        }
    }

    /// Scan over an exponent part of a floating-point literal.
    fn scan_float_exponent(&mut self) {
        assert!(is_digit(self.cur.unwrap(), 10) || self.cur_is('_'));

        let exponent_start = self.prev_pos;
        let exponent_digits = self.scan_digits(10, 10);

        if exponent_digits == 0 {
            self.report.error(Span::new(exponent_start, self.prev_pos),
                "The exponent contains no valid digits");
        }
    }

    /// Scan over a single character literal.
    fn scan_character_literal(&mut self) -> Token {
        use self::CharacterSpecials::{SingleQuote, UnexpectedTerminator};

        // A character literal is a single quote...
        self.expect_and_skip("\'");

        let terminated = match self.scan_one_character_of_character() {
            // ...followed by one character...
            Ok(_) => {
                match self.scan_one_character_of_character() {
                    // ...and then by another single quote.
                    Err(SingleQuote) => {
                        self.read();
                        true
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
                                        "A character literal must contain only one character");
                                    break;
                                }
                                // We did not see a closing quote on the same line, abort scanning
                                Err(UnexpectedTerminator) => {
                                    terminated = false;
                                    break;
                                }
                            }
                        }
                        terminated
                    }
                    Err(UnexpectedTerminator) => { false }
                }
            }
            // A literal single quote may be immediately followed by another literal single quote
            // in two cases: ''' (a correct character literal) and '' (incorrect empty character).
            Err(SingleQuote) => {
                self.read();
                if self.cur_is('\'') {
                    self.read();
                } else {
                    self.report.error(Span::new(self.start, self.prev_pos),
                        "A character literal must contain a character");
                }
                true
            }
            Err(UnexpectedTerminator) => { false }
        };

        if !terminated {
            self.report.error(Span::new(self.start, self.prev_pos),
                    "Missing closing single quote.");

            return Token::Unrecognized;
        }

        self.scan_optional_type_suffix();

        return Token::Character;
    }

    /// Scan over a string literal.
    fn scan_string(&mut self) -> Token {
        use self::StringSpecials::{DoubleQuote, SkippedEscapedLineEnding, UnexpectedTerminator};

        // Strings start with a double quote...
        self.expect_and_skip("\"");

        loop {
            match self.scan_one_character_of_string() {
                // ...then it contains some characters...
                Ok(_) => {
                    // (which we currently ignore)
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
                    self.report.error(Span::new(self.start, self.pos),
                        "Missing closing double quote.");

                    return Token::Unrecognized;
                }
            }
        }

        self.scan_optional_type_suffix();

        return Token::String;
    }

    /// Scan over an explicit symbol.
    fn scan_explicit_symbol(&mut self) -> Token {
        use self::SymbolSpecials::{Backquote, UnexpectedTerminator};

        // Symbols start with a backquote...
        self.expect_and_skip("`");

        loop {
            match self.scan_one_character_of_symbol() {
                // ...then we have some characters...
                Ok(_) => {
                    // (which we currently ignore)
                }
                // ...and finally the symbol ends with a closing backquote.
                Err(Backquote) => {
                    self.read();
                    break;
                }
                // But things go wrong sometimes and the symbol may not be terminated
                Err(UnexpectedTerminator) => {
                    self.report.error(Span::new(self.start, self.prev_pos),
                        "Missing closing backquote.");

                    return Token::Unrecognized;
                }
            }
        }

        return Token::ExplicitSymbol;
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
                        "Bare CR characters must be escaped");
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
                        "Bare CR characters must be escaped");
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
                        "Bare CR characters must be escaped");
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
                        "Bare CR character");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "Unknown escape sequence");
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
                        "Bare CR character");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "Unknown escape sequence");
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
                        "Bare CR character");
                }
                self.report.error(Span::new(self.prev_pos - 1, self.pos),
                    "Unknown escape sequence");
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

        let digits_start = self.prev_pos;
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
            self.report.error(Span::new(digits_start, digits_end),
                "Expected two hexadecimal digits.");
        } else {
            if value > 0x7F {
                self.report.error(Span::new(digits_start - 2, digits_end),
                    "\\x?? escapes can only be used for ASCII values");
            }
        }

        // The value may be incorrect, but this method is used only in character and string
        // contexts where we do not really care about this (from the lexical standpoint)
        return value as char;
    }

    /// Scan over a single Unicode escape sequence.
    ///
    /// Returns Some value of the escape sequence, or None if the sequence was legible
    /// but otherwise incorrect.
    fn scan_escape_unicode(&mut self, extra_delimiter: Option<char>) -> Option<char> {
        // Unicode escapes start with \u, we have already seen the backslash
        self.expect_and_skip("u");

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

        // Keep our mouth shut about missing/asymmetric braces if there is nothing in them anyway
        if empty_braces {
            self.report.error(Span::new(brace_start, brace_end),
                "Missing Unicode scalar value");
            return None;
        }

        match (missing_open, missing_close) {
            (true, false) => {
                self.report.error(Span::new(brace_start, brace_start),
                    "Unicode scalar value must start with '{'");
            }
            (false, true) => {
                self.report.error(Span::new(brace_end, brace_end),
                    "Unicode scalar value must end with '}'");
            }
            (true, true) => {
                self.report.error(Span::new(brace_start, brace_end),
                    "Unicode scalar value must be surrounded with '{' '}'"); // TODO: message
            }
            (false, false) => { }
        }

        if invalid_hex {
            self.report.error(Span::new(brace_start, brace_end),
                "Incorrect Unicode scalar value. Expected only hex digits");
            return None;
        }

        if unicode_overflow {
            self.report.error(Span::new(brace_start - 2, brace_end),
                "Incorrect Unicode scalar value. Out of range, too big"); // TODO: messages
            return None;
        }

        if (0xD800 <= value) && (value <= 0xDFFF) {
            self.report.error(Span::new(brace_start - 2, brace_end),
                "Incorrect Unicode scalar value. Surrogate"); // TODO: messages
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

        loop {
            match self.cur {
                Some('"') => {
                    if self.scan_raw_string_trailers(hash_count) {
                        break;
                    }
                }
                Some(c) => {
                    if c == '\r' && self.peek() != Some('\n') {
                        self.report.error(Span::new(self.prev_pos, self.pos),
                            "Bare CR character");
                    }
                    self.read();
                }
                None => {
                    self.report.error(Span::new(self.start, self.pos),
                        "Unexpected EOF. Expected end of raw string");
                    // TODO: output expected number of hashes

                    return Token::Unrecognized;
                }
            }
        }

        self.scan_optional_type_suffix();

        return Token::RawString;
    }

    /// Scan over raw string trailing sequence `"#...#`.
    ///
    /// Scanner stops either at the first non-`#` character, or at the end of file, or when
    /// `hash_count` hashes have been scanned over, whichever comes first.
    ///
    /// Returns `true` when a correct trailing sequence was scanned, and `false` if there
    /// were not enough hashes after the quote and the raw string content possibly goes on.
    /// (Possibly, because `false` is also returned when EOF is reached before the sufficient
    /// number of hashes are scanner over.)
    fn scan_raw_string_trailers(&mut self, hash_count: u32) -> bool {
        // Raw string content ends with an double quote
        self.expect_and_skip("\"");

        let mut seen = 0;

        while seen < hash_count {
            if self.cur_is('#') {
                seen += 1;
                self.read();
            } else {
                return false;
            }
        }

        return true;
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
            "Incomprehensible character sequence");

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

        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                // Well, okay, another character has been correctly scanned over
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Just go on scanning thw word if this a valid continuation
                    if category.is(WORD_CONTINUE) {
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
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => { }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "ASCII is not allowed in identifier Unicode fallback");
                }
                // Decimal digits are valid contiuations of word identifiers
                Err(Digit) => {
                    assert!(sash_identifiers::category_of(self.cur.unwrap()).is(WORD_CONTINUE));
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

        return Token::Identifier;
    }

    /// Scan over a standalone word identifier or maybe an implicit symbol which starts
    /// with `initial` character.
    fn scan_identifier_word_or_symbol(&mut self, initial: char) -> Token {
        let initial_token = self.scan_identifier_word(initial);

        // Word identifier followed by a single colon forms an implicit symbol token.
        if (self.cur_is(':')) && (self.peek() != Some(':')) {
            self.read();
            return Token::ImplicitSymbol;
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

        loop {
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                // Well, okay, another character has been correctly scanned over
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Just go on scanning thw word if this a valid continuation
                    if category.is(MARK_CONTINUE) {
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
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => { }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "ASCII is not allowed in identifier Unicode fallback");
                }
                // We have seen a literal dot. It is allowed in marks as long as it is followed by
                // at least one more literal dot. If that is the case, scan over all these dots.
                // Otherwise stop scanning the identifier without consuming this to-be-Token::Dot.
                Err(Dot) => {
                    if self.peek_is('.') {
                        while self.cur_is('.') {
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

        return Token::Identifier;
    }

    /// Scan over a quote identifier which starts with `initial` character.
    fn scan_identifier_quote(&mut self, initial: char) -> Token {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START, QUOTE_CONTINUE};
        use self::IdentifierSpecials::{Terminator, Dot, Digit, IncorrectUnicodeEscape,
            AsciiUnicodeEscape};

        // Quote identifiers must start with a proper starter
        assert!(sash_identifiers::category_of(initial).is(QUOTE_START));

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
                            "Combining modifiers are not allowed after quotes");
                    } else {
                        self.report.error(Span::new(old_prev_pos, self.prev_pos),
                            "Incorrect identifier character");
                    }
                }
                // The same is true for invalid Unicode escapes, just carry on scanning.
                // Don't report the error, the user already knows about malformed Unicode
                // which is obviously incorrect identifier character
                Err(IncorrectUnicodeEscape) => { }
                // For ASCII escapes it's also true, but we need a message
                Err(AsciiUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "ASCII is not allowed in identifier Unicode fallback");
                }
                // A clean termiantor of an identifier has been seen.
                // This includes decimal digits and dots for quote identifiers.
                Err(Dot) | Err(Terminator) | Err(Digit) => {
                    break;
                }
            }
        }

        return Token::Identifier;
    }

    /// Maybe scan over an optional type suffix of literal tokens.
    fn scan_optional_type_suffix(&mut self) {
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
                    self.scan_identifier_word(c);
                } else {
                    self.unread(c, old_prev_pos);
                }
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
    use tokens::{Token};
    use diagnostics::{Span, SpanReporter};

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
            ScannerTestSlice("/* forgot", Token::Unrecognized),
        ], &[Span::new(0, 9)], &[]);
    }

    #[test]
    fn block_comment_unterminated_2() {
        check(&[
            ScannerTestSlice("/*/", Token::Unrecognized),
        ], &[Span::new(0, 3)], &[]);
    }

    #[test]
    fn block_comment_unterminated_nested() {
        check(&[
            ScannerTestSlice("/*/*nested*/", Token::Unrecognized),
        ], &[Span::new(0, 12)], &[]);
    }

    #[test]
    fn block_comment_line_comment_allows_unterminated_blocks() {
        check(&[
            ScannerTestSlice("// /* doesn't matter", Token::Comment),
        ], &[], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Doc comments

    #[test]
    fn doc_comment_line() {
        check(&[
            ScannerTestSlice("/// Example\n",                                   Token::DocComment),
            ScannerTestSlice("/// Other line\r\n",                              Token::DocComment),
            ScannerTestSlice("/// More\n",                                      Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("//! Inner comments\n",                            Token::DocComment),
            ScannerTestSlice("//! Windows lines\r\n",                           Token::DocComment),
            ScannerTestSlice("\r\n",                                            Token::Whitespace),
            ScannerTestSlice("/// Mixed\n",                                     Token::DocComment),
            ScannerTestSlice("//! Mixed\r\n",                                   Token::DocComment),
        ], &[], &[]);
    }

    #[test]
    fn doc_comment_block() {
        check(&[
            ScannerTestSlice("/** Example */",                                  Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/** Multiple\n    lines\r\n    are allowed */",   Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/*! Some more\n    inner\r\n comments !*/",       Token::DocComment),
            ScannerTestSlice("\r\n",                                            Token::Whitespace),
            ScannerTestSlice("/*! and /*! they /** can */ be ****/ nested */",  Token::DocComment),
            ScannerTestSlice("/** in /*!! any */ way /* you */ like */",        Token::DocComment),
        ], &[], &[]);
    }

    #[test]
    fn doc_comment_intertype_nesting() {
        check(&[
            ScannerTestSlice("/// This /* is fine */\n",                        Token::DocComment),
            ScannerTestSlice("//! This /*! is too\r\n",                         Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/** Also // fine */",                             Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/*! Fine as well // */",                          Token::DocComment),
            ScannerTestSlice("\r\n",                                            Token::Whitespace),
            ScannerTestSlice("// /// These are also\n",                         Token::Comment),
            ScannerTestSlice("/* /** // fine */ */",                            Token::Comment),
        ], &[], &[]);
    }

    #[test]
    fn doc_comment_block_unterminated() {
        check(&[ScannerTestSlice("/** forgot ", Token::Unrecognized)], &[Span::new(0, 11)], &[]);
        check(&[ScannerTestSlice("/*! as well", Token::Unrecognized)], &[Span::new(0, 11)], &[]);
        check(&[ScannerTestSlice("/** /*nest",  Token::Unrecognized)], &[Span::new(0, 10)], &[]);
        check(&[ScannerTestSlice("/*!/*!*/",    Token::Unrecognized)], &[Span::new(0,  8)], &[]);
    }

    #[test]
    fn doc_comment_bare_crs() {
        check(&[
            ScannerTestSlice("/// bare crs\r///are errors\n",                   Token::DocComment),
            ScannerTestSlice("//! in all\r\r\rkinds of doc-comments\n",         Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/** and I mean \r all */",                        Token::DocComment),
            ScannerTestSlice("\r\n",                                            Token::Whitespace),
            ScannerTestSlice("/*! like /* \r this */ */",                       Token::DocComment),
        ], &[ Span::new( 12,  13), Span::new( 37,  38), Span::new( 38,  39), Span::new( 39,  40),
              Span::new( 78,  79), Span::new(100, 101),
        ], &[]);
    }

    #[test]
    fn doc_comment_non_docs() {
        check(&[
            ScannerTestSlice("/////////////////////////////////\n",             Token::Comment),
            ScannerTestSlice("// These are not doc comments\n",                 Token::Comment),
            ScannerTestSlice("/////////////////////////////////\n",             Token::Comment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/***\r\n * These are not as well\n ***/",         Token::Comment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("//!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!\n",              Token::DocComment),
            ScannerTestSlice("//! Though this is one\n",                        Token::DocComment),
            ScannerTestSlice("//!/////////////////////////////\n",              Token::DocComment),
            ScannerTestSlice(" \n ",                                            Token::Whitespace),
            ScannerTestSlice("/////////////////////////////////\n",             Token::Comment),
            ScannerTestSlice("/// It's a bit tricky...\n",                      Token::DocComment),
            ScannerTestSlice("/////////////////////////////////\n",             Token::Comment),
            ScannerTestSlice("\r\n",                                            Token::Whitespace),
            ScannerTestSlice("/// As well as this one, and this:\n",            Token::DocComment),
            ScannerTestSlice("///\n",                                           Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("/*!!! A doc-comment */",                          Token::DocComment),
            ScannerTestSlice("\r\t\n",                                          Token::Whitespace),
            ScannerTestSlice("/*!** A doc-comment as well **!*/",               Token::DocComment),
            ScannerTestSlice("\n",                                              Token::Whitespace),
            ScannerTestSlice("// This is not a doc comment:\n",                 Token::Comment),
            ScannerTestSlice("/**/",                                            Token::Comment),
            ScannerTestSlice("// But this one is:\r\n",                         Token::Comment),
            ScannerTestSlice("/*!*/",                                           Token::DocComment),
            ScannerTestSlice("// And this one isn't:\n",                        Token::Comment),
            ScannerTestSlice("/***/",                                           Token::Comment),
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
            ScannerTestSlice("#",  Token::Hash),
            ScannerTestSlice("#",  Token::Hash),
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

    #[test]
    fn integer_type_suffixes() {
        check(&[
            // ASCII suffixes
            ScannerTestSlice("1foo",                    Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("42i32",                   Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Only words can be suffixes
            ScannerTestSlice("42",                      Token::Integer),
            ScannerTestSlice("+",                       Token::Identifier),
            ScannerTestSlice("i32",                     Token::Identifier),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Leading zero is not special
            ScannerTestSlice("0yFFF",                   Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("0xBREAD",                 Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("0_o133",                  Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Unicode suffixes
            ScannerTestSlice("983\u{7206}\u{767A}",     Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("983\\u{7206}\\u{767A}",   Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // This is binary literal, not zero with suffix
            ScannerTestSlice("0b234",                   Token::Integer),
        ], &[ Span::new(71, 72), Span::new(72, 73), Span::new(73, 74) ], &[]);
    }

    #[test]
    fn integer_type_suffixes_invalid() {
        check(&[
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers. Note that underscores are treated
            // as a part of the number.
            ScannerTestSlice("45f\\u{D800}9",           Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("951_x\u{0}__",            Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("0000\\u430\\u443",        Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9_x\\u{78}__",            Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("542_o\\x10",              Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ScannerTestSlice("0000",                    Token::Integer),
            ScannerTestSlice("\u{0}\u{0}",              Token::Unrecognized),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("951__",                   Token::Integer),
            ScannerTestSlice("\u{0}",                   Token::Unrecognized),
            ScannerTestSlice("__",                      Token::Identifier),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9__",                     Token::Integer),
            ScannerTestSlice("\\u{DAAA}\\u{78}",        Token::Unrecognized),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("542_",                    Token::Integer),
            ScannerTestSlice("\\",                      Token::Unrecognized),
            ScannerTestSlice("x10",                     Token::Identifier),
        ], &[ Span::new( 3, 11), Span::new(18, 19), Span::new(28, 31), Span::new(33, 36),
              Span::new(40, 46), Span::new(54, 55), Span::new(63, 65), Span::new(71, 72),
              Span::new(78, 86), Span::new(78, 92), Span::new(97, 98)
        ], &[]);
    }

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

    #[test]
    fn float_type_suffixes() {
        check(&[
            // ASCII suffixes
            ScannerTestSlice("1.0zog",                      Token::Float),
            ScannerTestSlice(" ",                           Token::Whitespace),
            ScannerTestSlice("0e+10f32",                    Token::Float),
            ScannerTestSlice(" ",                           Token::Whitespace),
            // Only words can be suffixes
            ScannerTestSlice("56e",                         Token::Integer),
            ScannerTestSlice("=",                           Token::Identifier),
            ScannerTestSlice("_f64",                        Token::Identifier),
            ScannerTestSlice(" ",                           Token::Whitespace),
            // Unicode suffixes
            ScannerTestSlice("0.0_\u{7206}\u{767A}",        Token::Float),
            ScannerTestSlice(" ",                           Token::Whitespace),
            ScannerTestSlice("9.6E-7_8\\u{7206}\\u{767A}",  Token::Float),
            ScannerTestSlice(" ",                           Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn float_type_suffixes_invalid() {
        check(&[
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers. Note that underscores are treated
            // as a part of the number.
            ScannerTestSlice("4.5f\\u{D800}9",          Token::Float),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9e0_x\u{0}__",            Token::Float),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("0.000\\u{430\\u443}",     Token::Float),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9_e\\u{78}__",            Token::Integer),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("50_e+2_o\\\\10",          Token::Float),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ScannerTestSlice("00.0",                    Token::Float),
            ScannerTestSlice("\u{0}\u{1}",              Token::Unrecognized),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9.1_e+5_",                Token::Float),
            ScannerTestSlice("\u{5}",                   Token::Unrecognized),
            ScannerTestSlice("__",                      Token::Identifier),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("9E1_",                    Token::Float),
            ScannerTestSlice("\\u{DEAD}\\u{31}",        Token::Unrecognized),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("5.0_",                    Token::Float),
            ScannerTestSlice("\\",                      Token::Unrecognized),
            ScannerTestSlice("e10",                     Token::Identifier),
        ], &[ Span::new(  4,  12), Span::new( 19,  20), Span::new( 34,  34), Span::new( 36,  36),
              Span::new( 44,  50), Span::new( 61,  62), Span::new( 62,  63), Span::new( 70,  72),
              Span::new( 81,  82), Span::new( 89,  97), Span::new( 89, 103), Span::new(108, 109)
        ], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Characters

    #[test]
    fn character_ascii() {
        check(&[
            ScannerTestSlice("'a'",  Token::Character),
            ScannerTestSlice("   ",  Token::Whitespace),
            ScannerTestSlice("'b'",  Token::Character),
            ScannerTestSlice("   ",  Token::Whitespace),
            ScannerTestSlice("'0'",  Token::Character),
            ScannerTestSlice("   ",  Token::Whitespace),
            ScannerTestSlice("'''",  Token::Character),
            ScannerTestSlice("   ",  Token::Whitespace),
            ScannerTestSlice("' '",  Token::Character),
            ScannerTestSlice("   ",  Token::Whitespace),
            ScannerTestSlice("'''",  Token::Character),
            ScannerTestSlice("'''",  Token::Character),
            ScannerTestSlice("'\"'", Token::Character),
        ], &[], &[]);
    }

    #[test]
    fn character_unicode() {
        check(&[
            // Surrogates are not valid UTF-8 text and should have been reported before.
            // Rust does not even allow placing them into strings.
            ScannerTestSlice("'\u{0123}'",   Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'\u{07F7}'",   Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'\u{10ba}'",   Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'\u{B0e6}'",   Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'\u{100300}'", Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'\u{0103CA}'", Token::Character),
        ], &[], &[]);
    }

    #[test]
    fn character_control() {
        check(&[
            ScannerTestSlice("'\0'",   Token::Character),  // Control characters can be used in
            ScannerTestSlice(" ",      Token::Whitespace), // character literals (technically).
            ScannerTestSlice("'\t'",   Token::Character),  // They can be rendered weirdly by text
            ScannerTestSlice(" ",      Token::Whitespace), // editors, but we do not care much.
            ScannerTestSlice("'\x04'", Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice("'\x08'", Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice("'\x0B'", Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice("'\x7F'", Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice("'\u{2028}'", Token::Character),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("'\u{2029}'", Token::Character),
            ScannerTestSlice(" ",          Token::Whitespace),
            ScannerTestSlice("'\u{0086}'", Token::Character),
            ScannerTestSlice(" ",          Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn character_escape_sequences() {
        check(&[
            ScannerTestSlice(r"'\0'",  Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice(r"'\t'",  Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice(r"'\r'",  Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice(r"'\n'",  Token::Character),
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice(r"'\'",   Token::Character), // backslash alone is okay
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice(r"'\\'",  Token::Character), // escaped is fine as well
            ScannerTestSlice(" ",      Token::Whitespace),
            ScannerTestSlice("'\\\"'", Token::Character), // escaped double-quote
        ], &[], &[]);                                     // can be copy-pasted from strings
    }

    #[test]
    fn character_unicode_escapes() {
        check(&[
            ScannerTestSlice(r"'\x00'",         Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\x35'",         Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\x1f'",         Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\xFF'",         Token::Character),  // \x?? escapes are ASCII-only
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{12}'",       Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{d799}'",     Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{D800}'",     Token::Character),  // Surrogates are not valid
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{DEAD}'",     Token::Character),  // All of them
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{DFfF}'",     Token::Character),  // are not valid
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{e000}'",     Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{FFFE}'",     Token::Character),  // Non-characters are okay
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{fffff}'",    Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{F0123}'",    Token::Character),  // Private use area is okay
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{0}'",        Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{00000005}'", Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{99999999}'", Token::Character),  // Out of range are not okay
            ScannerTestSlice(r" ",              Token::Whitespace), // but they are still scanned
            ScannerTestSlice(r"'\u{f0f0f0deadbeef00012345}'", Token::Character),
        ], &[ Span::new( 22 , 26), Span::new( 49 , 57), Span::new(60, 68), Span::new(71, 79),
              Span::new(151, 163), Span::new(166, 192) ], &[]);
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
        check(&[
            ScannerTestSlice("'ab'",                Token::Character),
            ScannerTestSlice(" ",                   Token::Whitespace),
            ScannerTestSlice("'\u{00E6}\u{0113}'",  Token::Character),
            ScannerTestSlice(" ",                   Token::Whitespace),
            ScannerTestSlice(r"'\x31\x32'",         Token::Character),
            ScannerTestSlice(" ",                   Token::Whitespace),
            ScannerTestSlice(r"'\u{123}\u{4567}'",  Token::Character),
        ], &[ Span::new(0, 4), Span::new(5, 11), Span::new(12, 22), Span::new(23, 40) ], &[]);
    }

    #[test]
    fn character_missing_quotes() {
        check(&[
            ScannerTestSlice("'ab some + thing", Token::Unrecognized),
            ScannerTestSlice("\n",               Token::Whitespace),
            ScannerTestSlice("'''",              Token::Character),
            ScannerTestSlice("', more",          Token::Unrecognized),
            ScannerTestSlice("\r\n",             Token::Whitespace),
            ScannerTestSlice("''",               Token::Character), // special case
            ScannerTestSlice(",",                Token::Comma),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice(".",                Token::Dot),
            ScannerTestSlice("'test\rline'",     Token::Character),
            ScannerTestSlice("'another\rtest",   Token::Unrecognized),
        ], &[ Span::new( 0, 16), Span::new(20, 27), Span::new(29, 31), Span::new(39, 40),
              Span::new(34, 45), Span::new(53, 54), Span::new(45, 58) ], &[]);
    }

    #[test]
    fn character_premature_termination() {
        check(&[ ScannerTestSlice("'",      Token::Unrecognized) ], &[ Span::new(0, 1) ], &[]);
        check(&[ ScannerTestSlice("'a",     Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("'\\",    Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("'\t",    Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("'\\x",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                       Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("'\\y",   Token::Unrecognized) ], &[ Span::new(1, 3),
                                                                       Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("'\\u",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                       Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("'\\u{",  Token::Unrecognized) ], &[ Span::new(3, 4),
                                                                       Span::new(0, 4) ], &[]);
        check(&[ ScannerTestSlice("'\\u{}", Token::Unrecognized) ], &[ Span::new(3, 5),
                                                                       Span::new(0, 5) ], &[]);
    }

    #[test]
    fn character_bare_crs_and_line_endings() {
        check(&[
            // Bare carrige returns are reported as misplaced restricted characters
            ScannerTestSlice("'\r'",         Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'Carr\riage'", Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            // But proper line endings are treated as markers of missing closing quotes
            ScannerTestSlice("'",            Token::Unrecognized),
            ScannerTestSlice("\n",           Token::Whitespace),
            ScannerTestSlice("' '",          Token::Character),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("'",            Token::Unrecognized),
            ScannerTestSlice("\r\n",         Token::Whitespace),
            ScannerTestSlice("'",            Token::Unrecognized),
        ], &[ Span::new( 1,  2), Span::new( 9, 10), Span::new( 4, 15), Span::new(16, 17),
              Span::new(22, 23), Span::new(25, 26) ], &[]);
    }

    #[test]
    fn character_incorrect_unicode_escape_length() {
        check(&[
            ScannerTestSlice(r"'\x'",      Token::Character),
            ScannerTestSlice(r" ",         Token::Whitespace),
            ScannerTestSlice(r"'\x1'",     Token::Character),
            ScannerTestSlice(r" ",         Token::Whitespace),
            ScannerTestSlice(r"'\x123'",   Token::Character),
            ScannerTestSlice(r" ",         Token::Whitespace),
            ScannerTestSlice(r"'\u{}'",    Token::Character),
        ], &[ Span::new(3, 3), Span::new(8, 9), Span::new(14, 17), Span::new(22, 24) ], &[]);
    }

    // A similar heuristic is used for missing curly braces.
    // If character termination quote is seen before a brace, the brace is inserted.
    // If no character termination quote is found until the line ending, the whole literal
    // is considered unrecognized token with an error message about missing brace.
    //
    // TODO: the same as earlier

    #[test]
    fn character_incorrect_unicode_braces() {
        check(&[
            ScannerTestSlice(r"'\u{123'",               Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{'",                  Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{uiui}'",             Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{uiui'",              Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{some long string}'", Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{some long string'",  Token::Character),
            ScannerTestSlice(r" ",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{123, missing",       Token::Unrecognized),
            ScannerTestSlice("\n",                      Token::Whitespace),
            ScannerTestSlice(r"'\u{more missing",       Token::Unrecognized),
        ], &[ Span::new(  7,   7), Span::new(12,  13), Span::new(18, 24), Span::new( 34,  34),
              Span::new( 29,  34), Span::new(39,  57), Span::new(79, 79), Span::new( 62,  79),
              Span::new( 97,  97), Span::new(84,  97), Span::new(81, 97), Span::new(114, 114),
              Span::new(101, 114), Span::new(98, 114) ], &[]);
    }

    #[test]
    fn character_unicode_missing_digits() {
        check(&[
            ScannerTestSlice(r"'\u'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\u}'",      Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\uguu~'",   Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\ux\uy'",   Token::Character),
        ], &[ Span::new( 3,  3), Span::new( 8,  9), Span::new(14, 14), Span::new(11, 19),
              Span::new(23, 23), Span::new(26, 26), Span::new(20, 28),
        ], &[]);
    }

    #[test]
    fn character_unicode_bare_digits() {
        check(&[
            ScannerTestSlice(r"'\u0000'",       Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice(r"'\u9'",          Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice(r"'\uDEAD'",       Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice(r"'\u10F0F0'",     Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice(r"'\u9999999999'", Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice(r"'\u1\u2'",       Token::Character),
            ScannerTestSlice(" ",               Token::Whitespace),
        ], &[ Span::new( 3,  7), Span::new(12, 13), Span::new(18, 22), Span::new(16, 22),
              Span::new(27, 33), Span::new(38, 48), Span::new(36, 48), Span::new(53, 54),
              Span::new(56, 57), Span::new(50, 58),
        ], &[]);
    }

    #[test]
    fn character_unknown_escapes() {
        check(&[
            // Unsupported C escapes
            ScannerTestSlice(r"'\a'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\b'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\f'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\v'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\?'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),

            // Unsupported hell-knows-whats
            ScannerTestSlice(r"'\X9'",      Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\@'",       Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("'\\\u{0430}'", Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice(r"'\m\'",      Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),

            // Attempts at line-continuation
            ScannerTestSlice("'\\",         Token::Unrecognized),
            ScannerTestSlice("\n",          Token::Whitespace),
            ScannerTestSlice("' '",         Token::Character),
            ScannerTestSlice("  ",          Token::Whitespace),
            ScannerTestSlice("'foo\\",      Token::Unrecognized),
            ScannerTestSlice("\r\n",        Token::Whitespace),
            ScannerTestSlice("' '",         Token::Character),
            ScannerTestSlice("  ",          Token::Whitespace),
            ScannerTestSlice("'b\\\t\\",    Token::Unrecognized),
            ScannerTestSlice("\n\t",          Token::Whitespace),
            ScannerTestSlice("'",           Token::Unrecognized),
        ], &[ Span::new( 1,  3), Span::new( 6,  8), Span::new(11, 13), Span::new(16, 18),
              Span::new(21, 23), Span::new(26, 28), Span::new(25, 30), Span::new(32, 34),
              Span::new(37, 40), Span::new(43, 45), Span::new(42, 47), Span::new(48, 50),
              Span::new(56, 61), Span::new(70, 72), Span::new(68, 73), Span::new(75, 76),
        ], &[]);
    }

    #[test]
    fn character_type_suffixes() {
        check(&[
            // Suffixes are words
            ScannerTestSlice("'x'wide",                 Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\t'ASCII",               Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\\t'ASCII",              Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\u{3435}'_",             Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // And only words, symbols are not suffixes
            ScannerTestSlice("'='",                     Token::Character),
            ScannerTestSlice("=",                       Token::Identifier),
            ScannerTestSlice("'='",                     Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Unicode suffixes
            ScannerTestSlice("'\u{1F74}'\u{1F74}",      Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\\u{1F74}'\\u{1F74}",    Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn character_type_suffixes_invalid() {
        check(&[
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ScannerTestSlice("'\\u{EEEE}'\\u{47f}\\u{DAAA}",    Token::Character),
            ScannerTestSlice(" ",                               Token::Whitespace),
            ScannerTestSlice("'\\u{EEEE}'b\\u6Fx",              Token::Character),
            ScannerTestSlice(" ",                               Token::Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ScannerTestSlice("'0'",                     Token::Character),
            ScannerTestSlice("\\u0\\u1",                Token::Unrecognized),
            ScannerTestSlice("\t",                      Token::Whitespace),
            ScannerTestSlice("'\\u{F000}'",             Token::Character),
            ScannerTestSlice("\\u{F000}",               Token::Unrecognized),
            ScannerTestSlice("\t",                      Token::Whitespace),
            ScannerTestSlice("'f'",                     Token::Character),
            ScannerTestSlice("\\",                      Token::Unrecognized),
            ScannerTestSlice("x",                       Token::Identifier),
        ], &[ Span::new(17, 25), Span::new(39, 41), Span::new(37, 41), Span::new(48, 49),
              Span::new(51, 52), Span::new(46, 52), Span::new(63, 71), Span::new(75, 76),
        ], &[]);
    }

    #[test]
    fn character_type_suffixes_after_invalid() {
        check(&[
            // Type suffixes are scanned over just fine after invalid characters
            ScannerTestSlice("'\\u{DADA}'u32",          Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("''cc",                    Token::Character),
            ScannerTestSlice("''",                      Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\\u0'_\\u0",             Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\\5'q",                  Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'\r'foo",                 Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("'some'suffix",            Token::Character),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // But missing quotes are something else
            ScannerTestSlice("'foo",                    Token::Unrecognized),
            ScannerTestSlice("\n",                      Token::Whitespace),
            ScannerTestSlice("c32",                     Token::Identifier),
            ScannerTestSlice("\t",                      Token::Whitespace),
            ScannerTestSlice("'bar",                    Token::Unrecognized),
            ScannerTestSlice("\r\n",                    Token::Whitespace),
            ScannerTestSlice("'baz",                    Token::Unrecognized),
        ], &[ Span::new(  1,  9), Span::new( 14, 16), Span::new( 18, 20), Span::new( 24, 25),
              Span::new( 29, 30), Span::new( 27, 30), Span::new( 32, 34), Span::new( 38, 39),
              Span::new( 44, 50), Span::new( 57, 61), Span::new( 66, 70), Span::new( 72, 76),
        ], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Strings

    #[test]
    fn string_basic() {
        check(&[
            ScannerTestSlice(r#""""#,    Token::String),
            ScannerTestSlice(" ",        Token::Whitespace),
            ScannerTestSlice(r#"'"'"#,   Token::Character),
            ScannerTestSlice(r#""'""#,   Token::String),
            ScannerTestSlice(" ",        Token::Whitespace),
            ScannerTestSlice(r#""foo""#, Token::String),
            ScannerTestSlice(r#""bar""#, Token::String),
            ScannerTestSlice(" ",        Token::Whitespace),
            ScannerTestSlice(r#""`!@#$%^&*()_+:<>?';[]{}=""#, Token::String),
        ], &[], &[]);
    }

    #[test]
    fn string_unicode() {
        check(&[
            ScannerTestSlice("\"\u{0395}\u{03C9}\u{03C2}\u{03BD}\u{03B5}\"",        Token::String),
            ScannerTestSlice(" ",                                               Token::Whitespace),
            ScannerTestSlice("\"\u{041A}\u{044E}\u{043C}\u{043A}\u{0443}\"",        Token::String),
            ScannerTestSlice(" ",                                               Token::Whitespace),
            ScannerTestSlice("\"\u{4EE3}\u{3072}\u{5099}\u{9752}\u{8CBB}\"",        Token::String),
            ScannerTestSlice(" ",                                               Token::Whitespace),
            ScannerTestSlice("\"\u{0627}\u{0644}\u{062D}\u{0643}\u{0648}\u{0645}\"",Token::String),
            ScannerTestSlice(" ",                                               Token::Whitespace),
            ScannerTestSlice("\"\u{100100}\u{100200}\u{103000}\u{10FEEE}\u{FEFF}\"",Token::String),
        ], &[], &[]);
    }

    #[test]
    fn string_escapes() {
        check(&[
            // C-style escapes supported by characters
            ScannerTestSlice(r#""\0\t\r\n""#,    Token::String),
            // Double quotes and backslashes must be escaped in strings
            ScannerTestSlice(r#""\\\" \"\\\"""#, Token::String),
            // Nulls and tabs can be used unescaped
            ScannerTestSlice("\"\t\0\t \tx\0\"", Token::String),
        ], &[], &[]);
    }

    #[test]
    fn string_unicode_escapes() {
        check(&[
            // Strings support both byte escapes...
            ScannerTestSlice(r#""\x00\x3D\x70 \x50\x6E""#,   Token::String),
            // ...and Unicode escapes...
            ScannerTestSlice(r#""\u{3} \u{12F1E}\u{F0F0}""#, Token::String),
            // ...and, as with characters, somewhat care about their semantics.
            ScannerTestSlice(r#""\xFF\xFE\x00\xDE\xAD""#,    Token::String),
            ScannerTestSlice(r#""\u{D900}\u{F0F0F090909}""#, Token::String),
        ], &[ Span::new(49, 53), Span::new(53, 57), Span::new(61, 65), Span::new(65, 69),
              Span::new(71, 79), Span::new(79, 94) ], &[]);
    }

    #[test]
    fn string_multiline() {
        check(&[
            ScannerTestSlice("\"multiline\ndemo\"",            Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"windows\r\nline\r\nendings\"", Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"bare\rCR character\"",         Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"continuation\\\nstring\"",     Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"windows\\\r\ncontinuation\"",  Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"cont\\\n\t\t  with space\"",   Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"\\\r\n\none more time\"",      Token::String),
            ScannerTestSlice("\n",                             Token::Whitespace),
            ScannerTestSlice("\"but\\\rbare CR doesn't work\"", Token::String),
        ], &[ Span::new(47, 48), Span::new(158, 159), Span::new(157, 159) ], &[]);
    }

    #[test]
    fn string_premature_termination() {
        check(&[ ScannerTestSlice("\"",      Token::Unrecognized) ], &[ Span::new(0, 1) ], &[]);
        check(&[ ScannerTestSlice("\"a",     Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("\"\\",    Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("\"\t",    Token::Unrecognized) ], &[ Span::new(0, 2) ], &[]);
        check(&[ ScannerTestSlice("\"\\x",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                        Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("\"\\y",   Token::Unrecognized) ], &[ Span::new(1, 3),
                                                                        Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("\"\\u",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                        Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("\"\\u{",  Token::Unrecognized) ], &[ Span::new(3, 4),
                                                                        Span::new(0, 4) ], &[]);
        check(&[ ScannerTestSlice("\"\\u{}", Token::Unrecognized) ], &[ Span::new(3, 5),
                                                                        Span::new(0, 5) ], &[]);
    }

    #[test]
    fn string_incorrect_unicode_escape_length() {
        check(&[
            ScannerTestSlice(r#""\x""#,    Token::String),
            ScannerTestSlice(r#" "#,       Token::Whitespace),
            ScannerTestSlice(r#""\x1""#,   Token::String),
            ScannerTestSlice(r#" "#,       Token::Whitespace),
            ScannerTestSlice(r#""\x123""#, Token::String),
            ScannerTestSlice(r#" "#,       Token::Whitespace),
            ScannerTestSlice(r#""\u{}""#,  Token::String),
        ], &[ Span::new(3, 3), Span::new(8, 9), Span::new(14, 17), Span::new(22, 24) ], &[]);
    }

    #[test]
    fn string_incorrect_unicode_braces() {
        check(&[
            ScannerTestSlice(r#""\u{123""#,                                 Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{""#,                                    Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{uiui}""#,                               Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{uiui""#,                                Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{some long string}""#,                   Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{some long string""#,                    Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{123, missing\nsome text after that}\"", Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{456, missing\r\nsome more text\"",      Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{and bare carriage\rreturn}\"",          Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{line ends\\\n here}\"",                 Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{with this\\u{123}\"",                   Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice("\"\\u{or this\\f\"",                          Token::String),
            ScannerTestSlice(r#" "#,                                        Token::Whitespace),
            ScannerTestSlice(r#""\u{check missing"#,                        Token::Unrecognized),
        ], &[ Span::new(  7,   7), Span::new( 12,  13), Span::new( 18,  24), Span::new( 34,  34),
              Span::new( 29,  34), Span::new( 39,  57), Span::new( 79,  79), Span::new( 62,  79),
              Span::new( 97,  97), Span::new( 84,  97), Span::new(137, 137), Span::new(124, 137),
              Span::new(158, 184), Span::new(199, 199), Span::new(189, 199), Span::new(222, 222),
              Span::new(212, 222), Span::new(242, 242), Span::new(234, 242), Span::new(242, 244),
              Span::new(263, 263), Span::new(249, 263), Span::new(246, 263),
        ], &[]);
    }

    #[test]
    fn string_unicode_missing_opening() {
        check(&[
            ScannerTestSlice(r#""\u""#,       Token::String),
            ScannerTestSlice(" ",             Token::Whitespace),
            ScannerTestSlice(r#""\u}""#,      Token::String),
            ScannerTestSlice(" ",             Token::Whitespace),
            ScannerTestSlice(r#""\uguu~""#,   Token::String),
            ScannerTestSlice(" ",             Token::Whitespace),
            ScannerTestSlice(r#""\ux\uy""#,   Token::String),
        ], &[ Span::new(3, 3), Span::new(8, 9), Span::new(14, 14), Span::new(23, 23),
              Span::new(26, 26) ], &[]);
    }

    #[test]
    fn string_unicode_bare_digits() {
        check(&[
            ScannerTestSlice(r#""\u0000\u9\uDEAD\u101111\u99999999999\u1}\u""#, Token::String),
        ], &[ Span::new( 3,  7), Span::new( 9, 10), Span::new(12, 16), Span::new(10, 16),
              Span::new(18, 24), Span::new(26, 37), Span::new(24, 37), Span::new(39, 39),
              Span::new(43, 43),
        ], &[]);
    }

    #[test]
    fn string_unknown_escapes() {
        check(&[
            // Unsupported C escapes
            ScannerTestSlice("\"\\a\\b\\f\\v\\?\\'\"",    Token::String),
            // Unsupported hell-knows-whats
            ScannerTestSlice("\"\\X9\\!\\\u{0742}\\y\"",  Token::String),
        ], &[ Span::new( 1,  3), Span::new( 3,  5), Span::new( 5,  7), Span::new( 7,  9),
              Span::new( 9, 11), Span::new(11, 13), Span::new(15, 17), Span::new(18, 20),
              Span::new(20, 23), Span::new(23, 25), ], &[]);
    }

    // TODO: more tests

    #[test]
    fn string_type_suffixes() {
        check(&[
            // Suffixes are words
            ScannerTestSlice("\"x\"wide",               Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\t\"ASCII",             Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\\t\"ASCII",            Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\u{3435}\"_",           Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // And only words, symbols are not suffixes
            ScannerTestSlice("\"=\"",                   Token::String),
            ScannerTestSlice("==",                      Token::Identifier),
            ScannerTestSlice("\"=\"",                   Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Unicode suffixes
            ScannerTestSlice("\"\u{1F74}\"\u{1F74}",    Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\\u{1F74}\"\\u{1F74}",  Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn string_type_suffixes_invalid() {
        check(&[
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ScannerTestSlice("\"fofo\"\\u{47f}\\u{DAAA}",   Token::String),
            ScannerTestSlice("\"\"b\\u4Fx",                 Token::String),
            ScannerTestSlice(" ",                           Token::Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ScannerTestSlice("\"\\\"\"",                Token::String),
            ScannerTestSlice("\\u3F",                   Token::Unrecognized),
            ScannerTestSlice("\n",                      Token::Whitespace),
            ScannerTestSlice("\"\\u{F000}\\u{D800}\"",  Token::String),
            ScannerTestSlice("\\u{F000}",               Token::Unrecognized),
            ScannerTestSlice("\t",                      Token::Whitespace),
            ScannerTestSlice("\"foo\"",                 Token::String),
            ScannerTestSlice("\\",                      Token::Unrecognized),
            ScannerTestSlice("U900",                    Token::Identifier),
        ], &[ Span::new(13, 21), Span::new(26, 28), Span::new(24, 28), Span::new(36, 38),
              Span::new(34, 38), Span::new(48, 56), Span::new(57, 65), Span::new(71, 72),
        ], &[]);
    }

    #[test]
    fn string_type_suffixes_after_invalid() {
        check(&[
            // Type suffixes are scanned over just fine after invalid strings
            ScannerTestSlice("\"\\u0\"_\\u0",           Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\\5\"q",                Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\r\"foo",               Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\\x\"zog",              Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("\"\\x4500\"__",           Token::String),
            // We aren't able to test missing quotes as they are detected only at EOF
        ], &[ Span::new( 3,  4), Span::new( 8,  9), Span::new( 6,  9), Span::new(11, 13),
              Span::new(17, 18), Span::new(26, 26), Span::new(34, 38),
        ], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Raw strings

    #[test]
    fn raw_string_basic() {
        check(&[
            ScannerTestSlice("r\"\"",              Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"test\"",          Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"h\\a\\-\\h\\a\"", Token::RawString),
        ], &[], &[]);
    }

    #[test]
    fn raw_string_unicode() {
        check(&[
            ScannerTestSlice("r\"\u{0442}\u{044D}\u{0441}\u{0442}\"",
                                                   Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"\u{D1F}\u{D46}\u{D38}\u{D4D}\u{D31}\u{D4D}\u{D31}\u{D4D}\"",
                                                   Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"\u{0074}\u{0068}\u{1EED}\"",
                                                   Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"\u{10E2}\u{10D4}\u{10E1}\u{10E2}\u{10D8}\"",
                                                   Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"\u{100100}\u{100200}\u{103000}\\\u{10FEEE}\u{FEFF}\"",
                                                   Token::RawString),
        ], &[], &[]);
    }

    #[test]
    fn raw_string_hashed() {
        check(&[
            ScannerTestSlice("r\"#\"",             Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r\"##\"",            Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r#\"\"\"\"#",        Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r##\"\"#\"\"##",     Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r###################\"test\"###################", Token::RawString),
            ScannerTestSlice(" ",                  Token::Whitespace),
            ScannerTestSlice("r#\"<img src=\"some\test.jpg\"/>\"#", Token::RawString),
        ], &[], &[]);
    }

    #[test]
    fn raw_string_multiline() {
        check(&[
            ScannerTestSlice("r\"multi\nline\"",        Token::RawString),
            ScannerTestSlice(",",                       Token::Comma),
            ScannerTestSlice("r\"windows\r\nline\"",    Token::RawString),
            ScannerTestSlice(",",                       Token::Comma),
            ScannerTestSlice("r\"extra\n\n\npadding\"", Token::RawString),
            ScannerTestSlice(",",                       Token::Comma),
            ScannerTestSlice("r#\"\"\n\"\n\"#",         Token::RawString),
            ScannerTestSlice(",",                       Token::Comma),
            ScannerTestSlice("r##\"\r\n#\r\n\"##",      Token::RawString),
            ScannerTestSlice(",",                       Token::Comma),
            ScannerTestSlice("r\"line\\\nbreak\"",      Token::RawString), // These aren't escapes,
            ScannerTestSlice(",",                       Token::Comma),     // just some slashes
            ScannerTestSlice("r\"more\\\r\nbreak\"",    Token::RawString), // followed by a newline
        ], &[], &[]);
    }

    #[test]
    fn raw_string_invalid_escape_sequences() {
        check(&[
            ScannerTestSlice("r\"\\\"",                 Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\\u{1234}\"",         Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\u{foo}\\u}{\\ufo\"", Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\.\\9\\/\"",          Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\xXx\"",              Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\r\\#\\m\"",          Token::RawString),
        ], &[], &[]);
    }

    #[test]
    fn raw_string_premature_termination() {
        check(&[ScannerTestSlice("r\"",               Token::Unrecognized)],
              &[ Span::new(0, 2) ], &[]);
        check(&[ScannerTestSlice("r\"some text",      Token::Unrecognized)],
              &[ Span::new(0, 11) ], &[]);
        check(&[ScannerTestSlice("r\"line\n",         Token::Unrecognized)],
              &[ Span::new(0, 7) ], &[]);
        check(&[ScannerTestSlice("r\"windows\r\n",    Token::Unrecognized)],
              &[ Span::new(0, 11) ], &[]);
        check(&[ScannerTestSlice("r\"bare CR\r",      Token::Unrecognized)],
              &[ Span::new(9, 10), Span::new(0, 10) ], &[]);
        check(&[ScannerTestSlice("r#\"text\"",        Token::Unrecognized)],
              &[ Span::new(0, 8) ], &[]);
        check(&[ScannerTestSlice("r###\"te\"#xt\"##", Token::Unrecognized)],
              &[ Span::new(0, 14) ], &[]);
        check(&[ScannerTestSlice("r#\"r\"\"",         Token::Unrecognized)],
              &[ Span::new(0, 6) ], &[]);
    }

    #[test]
    fn raw_string_bare_cr() {
        check(&[
            ScannerTestSlice("r\"te\rst\"",         Token::RawString),
            ScannerTestSlice(" ",                   Token::Whitespace),
            ScannerTestSlice("r\"test\\\r\"",       Token::RawString),
            ScannerTestSlice(" ",                   Token::Whitespace),
            ScannerTestSlice("r#\"bare\r\r\rCR\"#", Token::RawString),
        ], &[ Span::new( 4,  5), Span::new(16, 17), Span::new(26, 27), Span::new(27, 28),
              Span::new(28, 29) ], &[]);
    }

    // TODO: more tests?
    //       Like, unrecognized starts of raw strings, "r#####foo"?
    //       However, maybe these should be parsed as invalid multipart identifiers.

    #[test]
    fn raw_string_type_suffixes() {
        check(&[
            // Suffixes are words
            ScannerTestSlice("r\"x\"wide",              Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r##\"\t\"##ASCII",        Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\t\"ASCII",           Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r#\"\u{3435}\"#_",        Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // And only words, symbols are not suffixes
            ScannerTestSlice("r\"=\"",                  Token::RawString),
            ScannerTestSlice("==",                      Token::Identifier),
            ScannerTestSlice("r\"=\"",                  Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Unicode suffixes
            ScannerTestSlice("r\"\u{1F74}\"\u{1F74}",   Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\\u{1F74}\"\\u{1F74}", Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            // Suffixes (like other tokens) are scanned over geedily, but there
            // is an exception for raw strings. In sequences /r"/ and /r#/, the
            // 'r' character is never considered a type suffix. However, it is
            // true only for the *first* 'r'. Everything else is scanned over
            // greedily as usual.
            ScannerTestSlice("r\"\"",                   Token::RawString),
            ScannerTestSlice("r\"\"rr",                 Token::RawString),
            ScannerTestSlice("\"\"",                    Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r#\"1\"#",                Token::RawString),
            ScannerTestSlice("r##\"x\"##",              Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("rawr",                    Token::Identifier),
            ScannerTestSlice("\"123\"",                 Token::String),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"x\"boar",              Token::RawString),
            ScannerTestSlice("#",                       Token::Hash),
            ScannerTestSlice("\"x\"",                   Token::String),
            ScannerTestSlice("#",                       Token::Hash),
        ], &[], &[]);
    }

    #[test]
    fn raw_string_type_suffixes_invalid() {
        check(&[
            // Inner invalid characters are treated as constituents of suffixes,
            // just as in regular identifiers.
            ScannerTestSlice("r\"fofo\"\\u{47f}\\u{DAAA}",  Token::RawString),
            ScannerTestSlice(" ",                           Token::Whitespace),
            ScannerTestSlice("r#\"\"#b\\u4Fx",              Token::RawString),
            ScannerTestSlice(" ",                           Token::Whitespace),
            // However, if a literal is immediately followed by an invalid characters
            // they are not scanned over in anticipation of suffix. They are instantly
            // treated as Token::Unrecognized following the literal
            ScannerTestSlice("r\"\\\"",                     Token::RawString),
            ScannerTestSlice("\\u3F",                       Token::Unrecognized),
            ScannerTestSlice("\n",                          Token::Whitespace),
            ScannerTestSlice("r##\"\\u{F000}\\u{D800}\"##", Token::RawString),
            ScannerTestSlice("\\u{F000}",                   Token::Unrecognized),
            ScannerTestSlice("\t",                          Token::Whitespace),
            ScannerTestSlice("r\"foo\"",                    Token::RawString),
            ScannerTestSlice("\\",                          Token::Unrecognized),
            ScannerTestSlice("U900",                        Token::Identifier),
            ScannerTestSlice("\n",                          Token::Whitespace),
            // Specifically for raw strings: \u{72} is not valid starter for them
            ScannerTestSlice("r#\"\"#",                     Token::RawString),
            ScannerTestSlice("\\u{72}",                     Token::Unrecognized),
            ScannerTestSlice("#",                           Token::Hash),
            ScannerTestSlice("\"4\"",                       Token::String),
            ScannerTestSlice("#",                           Token::Hash),
        ], &[ Span::new(14, 22), Span::new(31, 33), Span::new(29, 33), Span::new(41, 43),
              Span::new(39, 43), Span::new(67, 75), Span::new(82, 83), Span::new(93, 99),
        ], &[]);
    }

    #[test]
    fn raw_string_type_suffixes_after_invalid() {
        check(&[
            // Type suffixes are scanned over just fine after invalid strings
            ScannerTestSlice("r\"\\u0\"_\\u0",          Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r##\"\\5\"##q",           Token::RawString),
            ScannerTestSlice(" ",                       Token::Whitespace),
            ScannerTestSlice("r\"\r\"foo",              Token::RawString),
            // We aren't able to test missing quotes as they are detected only at EOF
        ], &[ Span::new( 9, 10), Span::new( 7, 10), Span::new(24, 25) ], &[]);
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Identifiers

    #[test]
    fn identifier_ascii_words() {
        check(&[
            ScannerTestSlice("word",         Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("_underscore_", Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("__",           Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("x1234567890",  Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("_9_",          Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("UpperCase",    Token::Identifier),
            ScannerTestSlice(" ",            Token::Whitespace),
            ScannerTestSlice("OMG11111",     Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_ascii_marks() {
        check(&[
            ScannerTestSlice("+",                Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("-",                Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("*",                Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("/",                Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("<=",               Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("=",                Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("==",               Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("..",               Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("...",              Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("..+..=../..*..",   Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("<$>",              Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("&&",               Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("??",               Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("+++",              Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("%/%",              Token::Identifier),
            ScannerTestSlice(" ",                Token::Whitespace),
            ScannerTestSlice("<$%&*+|-~/=@^>!?", Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_unicode_words() {
        check(&[
    // Lu, Ll, Lo
            ScannerTestSlice("\u{0054}\u{0068}\u{1EED}\u{005F}\u{006E}\u{0067}\u{0068}\u{0069}\
                              \u{1EC7}\u{006D}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0583}\u{0578}\u{0580}\u{0571}\u{0561}\u{0580}\u{056F}\u{0578}\
                              \u{0582}\u{0574}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0422}\u{0435}\u{0441}\u{0442}\u{0423}\u{0432}\u{0430}\u{043D}\
                              \u{043D}\u{042F}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{09AA}\u{09B0}\u{09C0}\u{0995}\u{09CD}\u{09B7}\u{09BE}\u{09AE}\
                              \u{09C2}\u{09B2}\u{0995}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{691C}\u{67FB}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}",    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1780}\u{17B6}\u{179A}\u{1792}\u{17D2}\u{179C}\u{17BE}\u{178F}\
                              \u{17C1}\u{179F}\u{17D2}\u{178F}",            Token::Identifier),

            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Lt
            ScannerTestSlice("\u{01F2}\u{0061}\u{0031}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1FAA}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Lm
            ScannerTestSlice("\u{1D2E}\u{1D43}\u{1D48}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{02C7}\u{02E4}\u{06E6}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Nl
            ScannerTestSlice("\u{2169}\u{216C}\u{2164}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{3007}\u{3007}\u{3007}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{12461}\u{12468}",                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Other_ID_Start
            ScannerTestSlice("\u{2118}\u{212E}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{212E}\u{2118}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Mn (continue)
            ScannerTestSlice("\u{0043}\u{0364}\u{0348}\u{0359}\u{0345}\u{032E}\u{0323}\u{035A}\
              \u{0074}\u{0342}\u{0351}\u{0351}\u{0309}\u{0363}\u{0301}\u{035E}\u{0331}\u{0325}\
              \u{032A}\u{034E}\u{0329}\u{031E}\u{0068}\u{035F}\u{0075}\u{0368}\u{0365}\u{0359}\
              \u{006C}\u{036E}\u{0307}\u{0358}\u{031E}\u{0356}\u{0329}\u{0330}\u{0326}\u{0068}\
              \u{0351}\u{030C}\u{0312}\u{0367}\u{033C}\u{035A}\u{0075}\u{0350}\u{034A}\u{036E}\
              \u{0336}\u{0329}\u{0320}\u{031E}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Mc (continue)
            ScannerTestSlice("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}",    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0932}\u{0902}\u{092C}\u{0947}\u{005F}\u{0938}\u{092E}\u{092F}\
                              \u{005F}\u{0924}\u{0915}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Nd (continue)
            ScannerTestSlice("\u{005F}\u{0661}\u{0665}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0996}\u{09BE}\u{09A6}\u{09CD}\u{09AF}\u{09E7}\u{0AE7}\u{0DE9}\
                              \u{1040}\u{A8D6}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Pc (continue)
            ScannerTestSlice("\u{0061}\u{203F}\u{0062}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0078}\u{FE4D}\u{0079}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{005F}\u{FE4F}\u{005F}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // Other_ID_Continue
            ScannerTestSlice("\u{0057}\u{00B7}\u{006F}\u{00B7}\u{0057}",    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1213}\u{121F}\u{1226}\u{1369}\u{136A}\u{136B}\u{136C}\u{136D}\
                              \u{136E}\u{136F}\u{1370}\u{1371}",            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{03A4}\u{0387}\u{03C1}\u{0387}\u{03BF}\u{0387}\u{03C6}\u{0387}\
                              \u{03AE}\u{0387}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0078}\u{19DA}",                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
    // ZWJ, ZWNJ
            ScannerTestSlice("\u{0CA8}\u{0CCD}\u{0CA8}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0CA8}\u{0CCD}\u{200C}\u{0CA8}",            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0915}\u{094D}\u{0937}",                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0915}\u{094D}\u{200D}\u{0937}",            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0645}\u{06CC}\u{200C}\u{062E}\u{0648}\u{0627}\u{0647}\u{0645}",
                                                                            Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_unicode_marks() {
        check(&[
    // Pd
            ScannerTestSlice("\u{2015}\u{301C}\u{FE31}\u{2010}\u{30A0}",Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Po
            ScannerTestSlice("\u{00B6}\u{066A}\u{1364}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2042}\u{2037}\u{203B}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{203C}\u{A8CE}\u{FE60}\u{FF0A}",        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{110BB}\u{111DD}\u{115C9}",             Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2025}",                                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2026}",                                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Sc
            ScannerTestSlice("\u{00A2}\u{00A5}\u{20A1}\u{0BF9}\u{20B8}\u{FE69}\u{FF04}",
                                                                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Sm
            ScannerTestSlice("\u{00D7}\u{207C}",                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2192}\u{2192}\u{2194}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{220F}\u{2230}",                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2257}",                                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{229D}\u{2AF7}\u{2AF5}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // So
            ScannerTestSlice("\u{00A9}\u{06DE}\u{0BF5}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{19FB}\u{19FF}",                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2127}\u{21B5}\u{21BA}",                Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2375}\u{236A}\u{2361}\u{2360}",        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{2569}\u{2566}\u{2573}\u{2588}",        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{25E9}\u{2625}\u{2639}\u{265B}\u{2690}",Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{26B5}\u{1D1E7}",                       Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{1D332}\u{1D354}\u{1D940}",             Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{1F300}\u{1F401}\u{1F423}\u{1F4B3}\u{1F980}",
                                                                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Mc (continue)
            ScannerTestSlice("\u{0021}\u{17BF}\u{0026}\u{0DDB}\u{002A}\u{0CCB}",
                                                                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Me (continue)
            ScannerTestSlice("\u{0024}\u{0488}",                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{003C}\u{20DD}\u{003E}\u{20DE}",        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
            ScannerTestSlice("\u{0021}\u{20DF}",                        Token::Identifier),
            ScannerTestSlice(" ",                                       Token::Whitespace),
    // Mn (continue)
            ScannerTestSlice("\u{227A}\u{0307}\u{0301}\u{0301}\u{030D}\u{030C}\u{0311}\u{033C}\
              \u{0353}\u{0359}\u{2203}\u{034F}\u{0317}\u{2202}\u{0363}\u{036B}\u{0342}\u{0342}\
              \u{035B}\u{031A}\u{0317}\u{033C}\u{0356}\u{031C}\u{0323}\u{2200}\u{033B}\u{033C}\
              \u{222D}\u{030E}\u{030F}\u{032D}\u{033A}",                Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_unicode_delimiters() {
        check(&[
    // Ps
            ScannerTestSlice("\u{2045}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2768}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2774}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{300E}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{FE3D}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{FE5D}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2987}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{3008}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
    // Pe
            ScannerTestSlice("\u{0F3B}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{0F3D}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{276B}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{300B}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{FE18}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{FF63}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2992}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
    // Pi
            ScannerTestSlice("\u{00AB}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{201B}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E02}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E09}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E1C}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E20}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
    // Pf
            ScannerTestSlice("\u{00BB}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E03}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{203A}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2E21}",    Token::Identifier),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("\u{2019}",    Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_escape_basic() {
        check(&[
            ScannerTestSlice(r"\u{0442}\u{0435}\u{0441}\u{0442}",           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u{01CB}\u{114D1}\u{114D2}\u{114D3}",        Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u{062A}\u{062C}\u{0631}\u{064A}\u{0628}",   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u{2026}\u{2026}\u{2026}",                   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u{00A9}\u{06DE}\u{0BF5}",                   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"demo\u{Ff11}\u{ff12}\u{fF13}",               Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{041F}\u{0440}\\u{043E}\u{0432}\u{0435}\\u{0440}\u{043A}\\u{0430}",
                                                                            Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("!\\u{20DF}",                                  Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_boundary_rules() {
        check(&[
    // Word | Mark
            ScannerTestSlice("a",                                           Token::Identifier),
            ScannerTestSlice("/",                                           Token::Identifier),
            ScannerTestSlice("b",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("x9",                                          Token::Identifier),
            ScannerTestSlice("..",                                          Token::Identifier),
            ScannerTestSlice("y",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("*",                                           Token::Identifier),
            ScannerTestSlice("_",                                           Token::Identifier),
            ScannerTestSlice("*",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{03BD}\u{03B5}\u{03C1}\u{03CC}",            Token::Identifier),
            ScannerTestSlice("\u{002B}",                                    Token::Identifier),
            ScannerTestSlice("\u{03C6}\u{03C9}\u{03C4}\u{03B9}\u{03AC}",    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{221A}",                                    Token::Identifier),
            ScannerTestSlice("\u{0078}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{222D}",                                    Token::Identifier),
            ScannerTestSlice("\u{092E}\u{094C}\u{091C}\u{093C}\u{093E}",    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{29BF}",                                    Token::Identifier),
            ScannerTestSlice("\u{006F}",                                    Token::Identifier),
            ScannerTestSlice("\u{29BF}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("<",                                           Token::Identifier),
            ScannerTestSlice("pre\u{0301}sident",                           Token::Identifier),
            ScannerTestSlice(">",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{003D}\u{033F}",                            Token::Identifier),
            ScannerTestSlice("\u{0078}\u{033F}",                            Token::Identifier),
            ScannerTestSlice("\u{003D}\u{033F}",                            Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Word | Quote
            ScannerTestSlice("\u{00AB}",                                    Token::Identifier),
            ScannerTestSlice("word",                                        Token::Identifier),
            ScannerTestSlice("\u{00BB}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{3008}",                                    Token::Identifier),
            ScannerTestSlice("x",                                           Token::Identifier),
            ScannerTestSlice("|",                                           Token::Identifier),
            ScannerTestSlice("y",                                           Token::Identifier),
            ScannerTestSlice("\u{3009}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{FE43}",                                    Token::Identifier),
            ScannerTestSlice("\u{3060}\u{307E}\u{3057}\u{307E}\u{3059}",    Token::Identifier),
            ScannerTestSlice("\u{FE44}",                                    Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Mark | Quote
            ScannerTestSlice("\u{0F3A}",                                    Token::Identifier),
            ScannerTestSlice("\u{2015}",                                    Token::Identifier),
            ScannerTestSlice("\u{0F3B}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{00A5}",                                    Token::Identifier),
            ScannerTestSlice("\u{301D}",                                    Token::Identifier),
            ScannerTestSlice("\u{00A5}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{228F}\u{0BC6}",                            Token::Identifier),
            ScannerTestSlice("\u{FE5D}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{FE3E}",                                    Token::Identifier),
            ScannerTestSlice("\u{27A4}",                                    Token::Identifier),
            ScannerTestSlice("\u{FE3E}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1F39B}\u{20E3}",                           Token::Identifier),
            ScannerTestSlice("\u{2E21}",                                    Token::Identifier),
            ScannerTestSlice("\u{1F39B}\u{20E3}",                           Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Quote | Quote
            ScannerTestSlice("\u{201D}",                                    Token::Identifier),
            ScannerTestSlice("\u{201D}",                                    Token::Identifier),
            ScannerTestSlice("\u{00AB}",                                    Token::Identifier),
            ScannerTestSlice("\u{00AB}",                                    Token::Identifier),
            ScannerTestSlice("\u{2039}",                                    Token::Identifier),
            ScannerTestSlice("\u{203A}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{2E21}",                                    Token::Identifier),
            ScannerTestSlice("\u{2045}",                                    Token::Identifier),
            ScannerTestSlice("\u{2770}",                                    Token::Identifier),
            ScannerTestSlice("\u{2770}",                                    Token::Identifier),
            ScannerTestSlice("\u{0F3D}",                                    Token::Identifier),
            ScannerTestSlice("\u{276F}",                                    Token::Identifier),
            ScannerTestSlice("\u{300F}",                                    Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_boundary_rules_escapes() {
        check(&[
    // Word | Mark
            ScannerTestSlice(r"a",                                          Token::Identifier),
            ScannerTestSlice(r"\u{2215}",                                   Token::Identifier),
            ScannerTestSlice(r"b",                                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u{29BF}",                                   Token::Identifier),
            ScannerTestSlice("\u{03BF}",                                    Token::Identifier),
            ScannerTestSlice("\\u{29BF}",                                   Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Word | Quote
            ScannerTestSlice(r"\u{00AB}",                                   Token::Identifier),
            ScannerTestSlice(r"w\u{2113}\u{1d466}d",                        Token::Identifier),
            ScannerTestSlice("\u{00BB}",                                    Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Mark | Quote
            ScannerTestSlice("\\u{1F39B}\u{20E3}",                          Token::Identifier),
            ScannerTestSlice("\u{2E21}",                                    Token::Identifier),
            ScannerTestSlice("\u{1F39B}\\u{20E3}",                          Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
    // Quote | Quote
            ScannerTestSlice("\u{2E21}",                                    Token::Identifier),
            ScannerTestSlice("\\u{2045}",                                   Token::Identifier),
            ScannerTestSlice("\u{2770}",                                    Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn identifier_escape_missing_braces() {
        check(&[
            // One can get away with just error messages when there are no braces
            // around otherwise correct scalar values
            ScannerTestSlice(r"\u0442\u0435\u0441\u0442",                   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u1794\u{17C3}\\u178F\\u{1784}",             Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // Even boundary detection rules work in this case
            ScannerTestSlice(r"\u212f}",                                    Token::Identifier),
            ScannerTestSlice(r"\u2212}",                                    Token::Identifier),
            ScannerTestSlice(r"\u2134}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u276E",                                     Token::Identifier),
            ScannerTestSlice(r"\u{72D7}",                                   Token::Identifier),
            ScannerTestSlice(r"\u300B",                                     Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // Given correct scalar values, we can also cope with missing starting/closing brace
            ScannerTestSlice(r"\u{221B\u2192}\u2192\u{2192\u2192",          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // However, if the starting Unicode escape is invalid, it is simply skipped over
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice(r"!",                                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice(r"g",                                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u{}",                                       Token::Unrecognized),
            ScannerTestSlice(r"==",                                         Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice("]",                                           Token::Rbrack),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u",                                         Token::Unrecognized),
            ScannerTestSlice("\u{301b}",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice(r"\u{301b}",                                   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // As in characters, line endings are used to detect missing closing braces
            ScannerTestSlice(r"\u{30C7}\u{30E2}\u{308",                     Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // And unexpected EOFs can happen with identifiers too, thought they are not fatal
            ScannerTestSlice(r"\u{914",                                     Token::Identifier),
        ], &[ Span::new(  2,   6), Span::new(  8,  12), Span::new( 14,  18), Span::new( 20,  24),
              Span::new( 27,  31), Span::new( 36,  40), Span::new( 51,  51), Span::new( 58,  58),
              Span::new( 65,  65), Span::new( 73,  77), Span::new( 87,  91), Span::new( 99,  99),
              Span::new(101, 101), Span::new(108, 112), Span::new(119, 119), Span::new(121, 125),
              Span::new(128, 128), Span::new(126, 128), Span::new(132, 132), Span::new(130, 132),
              Span::new(136, 138), Span::new(134, 138), Span::new(143, 143), Span::new(141, 143),
              Span::new(148, 148), Span::new(146, 148), Span::new(152, 152), Span::new(150, 152),
              Span::new(158, 158), Span::new(156, 158), Span::new(189, 189), Span::new(196, 196),
        ], &[]);
    }

    #[test]
    fn identifier_escape_invalid_values() {
        check(&[
            // As in characters or strings, missing values, surrogate code points, out-or-range
            // values, and non-scalar values are not okay
            ScannerTestSlice("fo\\u{}o",                                    Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("bar\\u{D900}",                                Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("b\\u{9999999999}az",                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("D\\u{COMBINING ACUTE ACCENT}mo",              Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // For boundary detection these are treated as valid values in whatever context we are
            ScannerTestSlice(r"\u{D800}\u{DDDD}",                           Token::Unrecognized),
            ScannerTestSlice(r"_1\u{DFFF}",                                 Token::Identifier),
            ScannerTestSlice(r"+\u{DEAD}\u{D912}",                          Token::Identifier),
            ScannerTestSlice(r"\u{2985}",                                   Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"\u{9999999999999}",                          Token::Unrecognized),
            ScannerTestSlice(r"==\u{Fo fo fo!}\u{a7}",                      Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // But invalid values are not start codes. For example, an entirely invalid sequence
            // will not count as an identifier. The digits that immediately follow it are a part
            // of a number, they do not count as XID_Continue which magically converts the whole
            // thing into a word identifier. The scanner never backtracks.
            ScannerTestSlice(r"\u{Some}\u{Invalid}\u{Stuff}",               Token::Unrecognized),
            ScannerTestSlice(r"123",                                        Token::Integer),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"\u{Some}\u{Invalid}\u{Stuff}",               Token::Unrecognized),
            ScannerTestSlice(r"_123",                                       Token::Identifier),
        ], &[ Span::new(  4,   6), Span::new( 11,  19), Span::new( 21,  35), Span::new( 41,  65),
              Span::new( 68,  76), Span::new( 76,  84), Span::new( 68,  84), Span::new( 86,  94),
              Span::new( 95, 103), Span::new(103, 111), Span::new(120, 137), Span::new(120, 137),
              Span::new(141, 152), Span::new(161, 167), Span::new(169, 178), Span::new(180, 187),
              Span::new(159, 187), Span::new(193, 199), Span::new(201, 210), Span::new(212, 219),
              Span::new(191, 219),
         ], &[]);
    }

    #[test]
    fn identifier_invalid_characters_plain() {
        check(&[
            // Arbitrary Unicode character sequences are considered invalid. Peculiar cases
            // in ASCII include control codes (other than whitespace), and  backslashes (\)
            // which are not immediately followed by 'u'. Non-ASCII cases include usage of
            // characters outside of identifier character set (e.g., general categories like
            // No, Sk, or C), or usage of bare identifier continuation characters (without
            // a starter character preceding them). The whole hunk of such invalid characters
            // is reported as Unrecognized.
            ScannerTestSlice("\u{00}\u{03}\u{04}\u{05}\u{06}\u{07}\u{08}",  Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{12}\u{1A}\u{1B}\u{1C}",                    Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1D}\u{1E}\u{1F}\u{7F}\u{80}\u{81}",        Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{82}\u{83}\u{84}",                          Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{e123}\u{F700}\u{FF000}\u{100000}",         Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{200B}\u{180E}\u{2062}\u{E0001}\u{E007F}",  Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\",                                          Token::Unrecognized),
            ScannerTestSlice("x12",                                         Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\\\",                                        Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("test\\",                                      Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0307}\u{09E3}\\\u{1DA61}\u{200D}",         Token::Unrecognized),
            ScannerTestSlice("1",                                           Token::Integer),
            ScannerTestSlice("\u{200C}\u{7F}\u{200D}",                      Token::Unrecognized),
            ScannerTestSlice("x\u{200D}y",                                  Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // However! The scanner tolerates invalid Unicode characters in the middle of
            // identifiers. They are still reported, but the scanning goes on afterwards
            // as if they were valid, including their usage for boundary detection.
            ScannerTestSlice("f\u{0}o",                                     Token::Identifier),
            ScannerTestSlice("+\u{E666}",                                   Token::Identifier),
            ScannerTestSlice("_\u{10}some\u{11}_\\invalid\\123",            Token::Identifier),
            ScannerTestSlice("==\u{02DC}==",                                Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("a\u{0488}b",                                  Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("C\u{20DD}_\u{20E3}",                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("+\u{200D}+=\u{200D}",                         Token::Identifier),
        ], &[ Span::new(  0,   7), Span::new(  8,  12), Span::new( 13,  21), Span::new( 22,  28),
              Span::new( 29,  43), Span::new( 44,  61), Span::new( 62,  63), Span::new( 67,  69),
              Span::new( 74,  75), Span::new( 76,  89), Span::new( 90,  97), Span::new(104, 105),
              Span::new(107, 110), Span::new(111, 112), Span::new(116, 117), Span::new(118, 119),
              Span::new(126, 127), Span::new(132, 134), Span::new(138, 140), Span::new(143, 146),
              Span::new(147, 150), Span::new(152, 155), Span::new(157, 160),
        ], &[]);
    }

    #[test]
    fn identifier_invalid_characters_escaped() {
        check(&[
            // The scanner also tolerates (i.e., is able to recover from) invalid escaped Unicode
            // characters in the middle of identifiers. This also includes surrogates (which can't
            // be embedded into Rust strings as is), and other invalid escapes.
            ScannerTestSlice(r"f\u{2000}o",                                 Token::Identifier),
            ScannerTestSlice(r"+\u{E666}",                                  Token::Identifier),
            ScannerTestSlice(r"_\u{60}some\u{7F}_\invalid\123",             Token::Identifier),
            ScannerTestSlice(r"==\u{02DC}==",                               Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"a\u{0488}b",                                 Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"C\u{20DD}_\u{20E3}",                         Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"+\u{200D}+=\u{200D}",                        Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"f\u{}o",                                     Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"f\u{REPLACEMENT CHARACTER}o",                Token::Identifier),
            ScannerTestSlice(r"+\uD900\uDDDD",                              Token::Identifier),
            ScannerTestSlice(r"_\u{9999999999999999}_",                     Token::Identifier),
        ], &[ Span::new(  1,   9), Span::new( 11,  19), Span::new( 20,  26), Span::new( 30,  36),
              Span::new( 37,  38), Span::new( 45,  46), Span::new( 51,  59), Span::new( 63,  71),
              Span::new( 74,  82), Span::new( 83,  91), Span::new( 93, 101), Span::new(103, 111),
              Span::new(115, 117), Span::new(122, 145), Span::new(149, 153), Span::new(147, 153),
              Span::new(155, 159), Span::new(153, 159), Span::new(160, 180),
        ], &[]);
    }

    #[test]
    fn identifier_unicode_ascii_escapes() {
        check(&[
            ScannerTestSlice(r"f\u{6F}o",                                   Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"example\u{2E}com",                           Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"\u{2E}\u{2E}\u{2E}",                         Token::Unrecognized),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"\u{2E}",                                     Token::Unrecognized),
            ScannerTestSlice(r".",                                          Token::Dot),
            ScannerTestSlice(r"\u{2E}",                                     Token::Unrecognized),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"c\u{31}2",                                   Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"test\u{0020}test",                           Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"a\u{2B}b",                                   Token::Identifier),
        ], &[ Span::new( 1,  7), Span::new(16, 22), Span::new(26, 44), Span::new(45, 51),
              Span::new(52, 58), Span::new(60, 66), Span::new(72, 80), Span::new(86, 92),
        ], &[]);
    }

    #[test]
    fn identifier_invalid_quote_modifiers() {
        check(&[
            // One peculiar case is usage of modifier characters after quote identifiers.
            // Instead of being reported as a separate Unrecognized token they are included
            // into the quote token (after getting reported, of course).
            ScannerTestSlice("\u{2045}\u{0488}",                            Token::Identifier),
            ScannerTestSlice("\u{276E}\u{0DDC}\u{16F7A}",                   Token::Identifier),
            ScannerTestSlice("\u{0F3D}\u{200D}\u{20DD}",                    Token::Identifier),
            ScannerTestSlice("\u{FE18}\u{093F}\u{0A3F}",                    Token::Identifier),
            ScannerTestSlice("\u{00AB}\u{0324}\u{0483}",                    Token::Identifier),
            ScannerTestSlice("\u{2039}\u{0CC7}",                            Token::Identifier),
            ScannerTestSlice("\u{2019}\u{20E2}",                            Token::Identifier),
            ScannerTestSlice("\u{2E0A}\u{17CA}\u{200C}\u{1B3C}",            Token::Identifier),
        ], &[ Span::new( 3,  5), Span::new( 8, 11), Span::new(11, 15), Span::new(18, 21),
              Span::new(21, 24), Span::new(27, 30), Span::new(30, 33), Span::new(35, 37),
              Span::new(37, 39), Span::new(42, 45), Span::new(48, 51), Span::new(54, 57),
              Span::new(57, 60), Span::new(60, 63),
        ], &[]);
    }

    #[test]
    fn identifier_special_raw_strings() {
        check(&[
            // Raw strings start with an 'r' which is a valid starter of word identifiers.
            // We must not confuse them.
            ScannerTestSlice("r\"awr\"",        Token::RawString),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("ra",              Token::Identifier),
            ScannerTestSlice("\"wr\"",          Token::String),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("raaaaa",          Token::Identifier),
            ScannerTestSlice("#",               Token::Hash),
            ScannerTestSlice("#",               Token::Hash),
            ScannerTestSlice("\"wr\"",          Token::String),
            ScannerTestSlice("#",               Token::Hash),
            ScannerTestSlice("#",               Token::Hash),
            ScannerTestSlice(" ",               Token::Whitespace),
            ScannerTestSlice("r#\"awr\"#",      Token::RawString),
        ], &[], &[]);
    }

    // TODO: boundary tests between all token types

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Symbols

    #[test]
    fn symbol_implicit() {
        check(&[
            // Implicit symbols are word identifiers followed by a single literal colon.
            // For example, ASCII words are fine:
            ScannerTestSlice("foo:",                                        Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("Symbol:",                                     Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("_:",                                          Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("_1:",                                         Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // Unicode words are fine too:
            ScannerTestSlice("\u{691C}\u{67FB}:",                           Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{1FAA}:",                                   Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{3007}\u{3007}\u{3007}:",                   Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{212E}\u{2118}:",                           Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{09A6}\u{09C0}\u{09B0}\u{09CD}\u{0998}:",   Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // As well as escaped ones:
            ScannerTestSlice("\u{005F}\\u{0661}\\u{0665}:",                 Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{005F}\\u{FE4F}\u{005F}:",                  Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0078}\\u{19DA}:",                          Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u{0915}\u{094D}\\u{0937}:",                 Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u{1FAA}:",                                  Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
        ], &[], &[]);
    }

    #[test]
    fn symbol_implicit_boundaries() {
        check(&[
            // Only a single colon forms a boundary for a symbol. It can be followed by anything
            // except for another colon, in which case we see a word identifier followed by
            // a double colon.
            ScannerTestSlice("foo:",                                        Token::ImplicitSymbol),
            ScannerTestSlice("+",                                           Token::Identifier),
            ScannerTestSlice("bar",                                         Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("x:",                                          Token::ImplicitSymbol),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            ScannerTestSlice("y:",                                          Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("z:",                                          Token::ImplicitSymbol),
            ScannerTestSlice("':'",                                         Token::Character),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("_:",                                          Token::ImplicitSymbol),
            ScannerTestSlice("10",                                          Token::Integer),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("zork",                                        Token::Identifier),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice("x",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // Also, only word identifiers can be implicit symbols
            ScannerTestSlice("++",                                          Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("$",                                           Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice(";",                                           Token::Semicolon),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("[",                                           Token::Lbrack),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("]",                                           Token::Rbrack),
            ScannerTestSlice("\u{2025}",                                    Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0024}\u{0488}",                            Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("\u{FE18}",                                    Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("\u{300E}",                                    Token::Identifier),
            // This includes escaped identifiers
            ScannerTestSlice("\u{220F}\\u{2230}",                           Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("\u{19FB}\u{19FF}",                            Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u{26B5}\\u{1D1E7}",                         Token::Identifier),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice("\\u{2E02}",                                   Token::Identifier),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u{2E21}",                                   Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // Finally, implicit symbols do not allow type suffixes
            ScannerTestSlice("foo:",                                        Token::ImplicitSymbol),
            ScannerTestSlice("bar",                                         Token::Identifier),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice("baz:",                                        Token::ImplicitSymbol),
            ScannerTestSlice("_",                                           Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // And cannot 'steal' others' suffixes
            ScannerTestSlice("123foo",                                      Token::Integer),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("bar:",                                        Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("'x'x",                                        Token::Character),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice("y",                                           Token::Identifier),
        ], &[], &[]);
    }

    #[test]
    fn symbol_implicit_invalid_characters() {
        check(&[
            // Invalid Unicode escapes and characters in symbols are reported as usual
            ScannerTestSlice("a\\u{0488}b:",                                Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("a\u{0488}b:",                                 Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("example\\u{2E}com:",                          Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("f\\u{REPLACEMENT CHARACTER}o:",               Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("w\\u2113\\u1d466d:",                          Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("C\u{20DD}_\u{20E3}:",                         Token::ImplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("test\\u{003A}:",                              Token::ImplicitSymbol),
        ], &[ Span::new(  1,   9), Span::new( 13,  15), Span::new( 25,  31), Span::new( 39,  62),
              Span::new( 68,  72), Span::new( 74,  80), Span::new( 72,  80), Span::new( 83,  86),
              Span::new( 87,  90), Span::new( 96, 104),
        ], &[]);
    }

    #[test]
    fn symbol_explicit() {
        check(&[
            // Explicit symbols look like strings quoted with backquotes
            ScannerTestSlice("`foo`",                                       Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`one two three`",                             Token::ExplicitSymbol),
            ScannerTestSlice("`1-2-3`",                                     Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`'\"'`",                                      Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("``",                                          Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // They can contain Unicode and support all character escape sequences,
            // plus an additional escape sequence for the backquote character
            ScannerTestSlice("`\\0\\t\\r\\n\\\\\\\"`",                      Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`\u{3053}\u{3093}\u{306B}\u{3061}\u{306F}`",  Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`\\u{05E9}\\u{05DC}\\u{05D5}\\u{05DD}`",      Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`\x00\x32`",                                  Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`///*//*/`",                                  Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`\\`...\\``",                                 Token::ExplicitSymbol),
        ], &[], &[]);
    }

    #[test]
    fn symbol_explicit_invalid_escapes() {
        check(&[
            // Invalid escape sequences in explicit symbols are reported as in string literals
            ScannerTestSlice(r"`\u{123\u456}\u{testing...}`",               Token::ExplicitSymbol),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"`\uguu\uDEAD\uF0F0F0F0F0F0F0F0\u`",          Token::ExplicitSymbol),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"`\a\b\f\v\?\'`",                             Token::ExplicitSymbol),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"`\x\x1\x1234`",                              Token::ExplicitSymbol),
        ], &[ Span::new( 7,  7), Span::new( 9,  9), Span::new(15, 27), Span::new(32, 32),
              Span::new(37, 41), Span::new(35, 41), Span::new(43, 59), Span::new(41, 59),
              Span::new(61, 61), Span::new(64, 66), Span::new(66, 68), Span::new(68, 70),
              Span::new(70, 72), Span::new(72, 74), Span::new(74, 76), Span::new(81, 81),
              Span::new(83, 84), Span::new(86, 90),
        ], &[]);
    }

    #[test]
    fn symbol_explicit_invalid_mulitline() {
        check(&[
            // Explicit symbols cannot span multiple lines. They are handled similar to character
            // literals. Though, one can embed newline characters into them via escape sequences.
            ScannerTestSlice("`example",                                    Token::Unrecognized),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            ScannerTestSlice("`some more",                                  Token::Unrecognized),
            ScannerTestSlice("\r\n",                                        Token::Whitespace),
            ScannerTestSlice("`Old\rApple`",                                Token::ExplicitSymbol),
            ScannerTestSlice("`",                                           Token::Unrecognized),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            ScannerTestSlice("`",                                           Token::Unrecognized),
            ScannerTestSlice("\r\n",                                        Token::Whitespace),
            ScannerTestSlice("`\r`",                                        Token::ExplicitSymbol),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            ScannerTestSlice("`\\",                                         Token::Unrecognized),
            ScannerTestSlice("\n\t",                                        Token::Whitespace),
            ScannerTestSlice("test",                                        Token::Identifier),
            ScannerTestSlice("`",                                           Token::Unrecognized),
        ], &[ Span::new( 0,  8), Span::new( 9, 19), Span::new(25, 26), Span::new(32, 33),
              Span::new(34, 35), Span::new(38, 39), Span::new(41, 43), Span::new(49, 50),
        ], &[]);
    }

    #[test]
    fn symbol_explicit_premature_termination() {
        // Unexpected EOFs are handled similar to characters and strings
        check(&[ ScannerTestSlice("`",      Token::Unrecognized) ], &[ Span::new(0, 1) ], &[]);
        check(&[ ScannerTestSlice("`xyz",   Token::Unrecognized) ], &[ Span::new(0, 4) ], &[]);
        check(&[ ScannerTestSlice("`\\x",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                       Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("`\\u",   Token::Unrecognized) ], &[ Span::new(3, 3),
                                                                       Span::new(0, 3) ], &[]);
        check(&[ ScannerTestSlice("`\\u{1", Token::Unrecognized) ], &[ Span::new(5, 5),
                                                                       Span::new(0, 5) ], &[]);
    }

    #[test]
    fn symbol_explicit_no_type_suffixes() {
        check(&[
            // Explicit symbols do not have type suffixes. They are terminated right after the
            // backquote.
            ScannerTestSlice("`foo`",                                       Token::ExplicitSymbol),
            ScannerTestSlice("bar",                                         Token::Identifier),
            ScannerTestSlice("`baz`",                                       Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`o`",                                         Token::ExplicitSymbol),
            ScannerTestSlice("r\"a\"",                                      Token::RawString),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`x`",                                         Token::ExplicitSymbol),
            ScannerTestSlice("'y'",                                         Token::Character),
            ScannerTestSlice("\"z\"",                                       Token::String),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("``",                                          Token::ExplicitSymbol),
            ScannerTestSlice("+",                                           Token::Identifier),
            ScannerTestSlice("``",                                          Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`.`",                                         Token::ExplicitSymbol),
            ScannerTestSlice(".",                                           Token::Dot),
            ScannerTestSlice("`.`",                                         Token::ExplicitSymbol),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`:`",                                         Token::ExplicitSymbol),
            ScannerTestSlice(":",                                           Token::Colon),
            ScannerTestSlice("e",                                           Token::Identifier),
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
