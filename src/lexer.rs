// Copyright (c) 2015, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

use std::mem;
use std::char;

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

    /// A single character
    Character,

    /// A string of characters
    String,

    /// A raw string of characters
    RawString,

    /// An identifier (of any kind)
    Identifier,

    /// Marker token denoting invalid character sequences
    Unrecognized,
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
            '/' if self.peek() == Some('/') => {
                self.scan_line_comment();
            }
            '/' if self.peek() == Some('*') => {
                self.scan_block_comment();
            }
            '(' => { self.read(); self.tok = Token::Lparen; }
            ')' => { self.read(); self.tok = Token::Rparen; }
            '[' => { self.read(); self.tok = Token::Lbrack; }
            ']' => { self.read(); self.tok = Token::Rbrack; }
            '{' => { self.read(); self.tok = Token::Lbrace; }
            '}' => { self.read(); self.tok = Token::Rbrace; }
            ',' => { self.read(); self.tok = Token::Comma; }
            ';' => { self.read(); self.tok = Token::Semicolon; }
            '.' if self.peek() != Some('.') => {
                self.read();
                self.tok = Token::Dot;
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
            '\'' => {
                self.scan_character_literal();
            }
            '"' => {
                self.scan_string();
            }
            'r' => {
                match self.scan_raw_string_leaders() {
                    Some(hashes) => {
                        self.scan_raw_string(hashes);
                    }
                    None => {
                        panic!("possibly invalid multipart identifier");
                    }
                }
            }
            _ => {
                self.scan_identifier();
            }
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

            self.tok = Token::Unrecognized;
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
                // with '+' or '-' being a part of some mark-identifier that follows.
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

    /// Scan over a single character literal
    fn scan_character_literal(&mut self) {
        use self::CharacterSpecials::*;

        // A character literal is a single quote...
        assert!(self.cur == Some('\''));
        self.read();

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
                if self.cur == Some('\'') {
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
            self.tok = Token::Unrecognized;
            return;
        }

        // TODO: type suffix

        self.tok = Token::Character;
    }

    /// Scan over a string literal
    fn scan_string(&mut self) {
        use self::StringSpecials::*;

        // Strings start with a double quote...
        assert!(self.cur == Some('"'));
        self.read();

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
                    self.tok = Token::Unrecognized;
                    return;
                }
            }
        }

        // TODO: type suffix

        self.tok = Token::String;
    }

    /// Scan over a single character or escape sequence for a character literal. Returns an Ok
    /// character if it was scanned successfully, or a special indicator value if there was no
    /// character to scan. Note that there is a difference between 'successfully scanned over
    /// a character or an escape sequence' and 'scanned over a correct and valid character token'.
    fn scan_one_character_of_character(&mut self) -> Result<char, CharacterSpecials> {
        use self::CharacterSpecials::*;
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
            Some('\r') if self.peek() == Some('\n') => {
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

    /// Scan over a single character or escape sequence for a string literal. Returns an Ok
    /// character if it was scanned successfully, or a special indicator value if there was no
    /// character to scan. Note that there is a difference between 'successfully scanned over
    /// a character or an escape sequence' and 'scanned over a correct and valid string token'.
    fn scan_one_character_of_string(&mut self) -> Result<char, StringSpecials> {
        use self::StringSpecials::*;
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
            Some('\r') if self.peek() == Some('\n') => {
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

    /// Scan over a single character or escape sequence for an identifier. Returns an Ok character
    /// if it was scanned successfully, or a special indicator value if there was no character to
    /// scan. Note that there is a difference between 'successfully scanned over a character or
    /// an escape sequence' and 'scanned over a correct and valid identifier'.
    fn scan_one_character_of_identifier(&mut self) -> Result<char, IdentifierSpecials> {
        use self::IdentifierSpecials::*;
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
            Some('\t') | None => {
                return Err(Terminator);
            }
            // There are a couple of exceptions, though. Comments are delimited by characters from
            // mark identifier set. However, sequences "/*" and "//" are not allowed in them.
            // Non-mark identifiers form a boundary when followed by these characters
            Some('/') if (self.peek() == Some('/') || self.peek() == Some('*')) => {
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

    /// Scan over an escape sequence allowed in character literals. Returns an Ok value denoted
    /// by the sequence (which is not guaranteed to be accurate), or a special indicator value.
    fn scan_character_escape_sequence(&mut self) -> Result<char, CharacterSpecials> {
        // All escape sequences start with a backslash
        assert!(self.cur == Some('\\'));
        self.read();

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
            Some('\r') if self.peek() == Some('\n') => {
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

    /// Scan over an escape sequence allowed in string literals. Returns an Ok value denoted
    /// by the sequence (which is not guaranteed to be accurate), or a special indicator value.
    fn scan_string_escape_sequence(&mut self) -> Result<char, StringSpecials> {
        use self::StringSpecials::*;

        // All escape sequences start with a backslash
        assert!(self.cur == Some('\\'));
        self.read();

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
            Some('\r') if self.peek() == Some('\n') => {
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

    /// Scan over an escape sequence allowed in identifiers. Returns an Ok value denoted by
    /// the sequence (which is not guaranteed to be accurate), or a special indicator value.
    fn scan_identifier_escape_sequence(&mut self) -> Result<char, IdentifierSpecials> {
        use self::IdentifierSpecials::*;

        // All escape sequences start with a backslash
        assert!(self.cur == Some('\\'));
        self.read();

        match self.cur {
            // \u... is a universal marker of a Unicode escape
            Some('u') => {
                let old_prev_pos = self.prev_pos;
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
            _ => {
                return Err(IncorrectUnicodeEscape);
            }
        }
    }

    /// Scan over a single byte escape sequence. Returns its value.
    fn scan_escape_byte(&mut self) -> char {
        assert!(self.cur == Some('x'));
        self.read();

        let mut digits = 0;
        let mut value: u8 = 0;

        let digits_start = self.prev_pos;
        while !self.at_eof() {
            let c = self.cur.unwrap();
            if !StringScanner::is_digit(c, 16) {
                break;
            }
            // We don't care about overflows here as they can only be caused by
            // reading more that two non-zero digits which is already an error.
            value = value.wrapping_shl(4) | StringScanner::hex_value(c);
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

    /// Scan over a single Unicode escape sequence. Returns Some value of the escape sequence,
    /// or None if the sequence was legible but otherwise incorrect.
    fn scan_escape_unicode(&mut self, extra_delimiter: Option<char>) -> Option<char> {
        assert!(self.cur == Some('u'));
        self.read();

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
                Some('\r') if self.peek() == Some('\n') => {
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
                    let valid_digit = StringScanner::is_digit(c, 16);

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
                        value = (value << 4) | (StringScanner::hex_value(c) as u32);
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

    /// Convert an ASCII hex digit character to its numeric value
    fn hex_value(c: char) -> u8 {
        assert!(StringScanner::is_digit(c, 16));

        const H: &'static [u8; 128] = &[
            0, 0, 0, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            0, 0, 0, 0, 0, 0, 0,0,0,0,0,0,0,0,0,0,0,1,2,3,4,5,6,7,8,9,0,0,0,0,0,0,
            0,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
            0,10,11,12,13,14,15,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,
        ];

        return H[c as usize];
    }

    /// Scan over raw string leading sequence `r#...#"`, stopping at the first non-leading
    /// character. Returns Some number of hashes scanned over in case of success, or None
    /// if the string did not look like a raw string leading sequence.
    fn scan_raw_string_leaders(&mut self) -> Option<u32> {
        assert!(self.cur == Some('r'));
        self.read();

        let mut hash_count = 0;
        while !self.at_eof() {
            match self.cur.unwrap() {
                '#' => { hash_count += 1; }
                '"' => { return Some(hash_count); }
                 _  => { break; }
            }
            self.read();
        }
        return None;
    }

    /// Scan over a raw string delimited by `hash_count` hashes
    fn scan_raw_string(&mut self, hash_count: u32) {
        assert!(self.cur == Some('"'));
        self.read();

        loop {
            match self.cur {
                Some('"') => {
                    if self.scan_raw_string_trailers(hash_count) {
                        self.tok = Token::RawString;
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
                    self.tok = Token::Unrecognized;
                    return;
                }
            }
        }

        // TODO: type suffix
    }

    /// Scan over raw string trailing sequence `"#...#`, stopping either at the first non-`#`
    /// character, or at the end of file, or when `hash_count` hashes have been scanned over,
    /// whichever comes first. Returns `true` when a correct trailing sequence was scanned.
    fn scan_raw_string_trailers(&mut self, hash_count: u32) -> bool {
        assert!(self.cur == Some('"'));
        self.read();

        let mut seen = 0;

        while seen < hash_count {
            if self.cur == Some('#') {
                seen += 1;
                self.read();
            } else {
                return false;
            }
        }

        return true;
    }

    /// Scan over an identifier
    fn scan_identifier(&mut self) {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START};
        use self::IdentifierSpecials::*;

        let mut seen_start = false;

        loop {
            // Look at the first character and try to decide what to do next
            let old_prev_pos = self.prev_pos;
            match self.scan_one_character_of_identifier() {
                Ok(c) => {
                    let category = sash_identifiers::category_of(c);

                    // Dispatch to the kind-specific loops based on the starter character
                    if category.is(WORD_START) {
                        seen_start = true;
                        self.scan_identifier_word(c);
                        break;
                    }
                    if category.is(MARK_START) {
                        seen_start = true;
                        self.scan_identifier_mark(c);
                        break;
                    }
                    if category.is(QUOTE_START) {
                        seen_start = true;
                        self.scan_identifier_quote(c);
                        break;
                    }

                    // If this does not seem to be a valid starter character, continue scanning
                    // in hope that this one was a mistake and some proper starter will show up
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // The same is true for invalid Unicode escapes, just carry on scanning
                Err(IncorrectUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // For ASCII escapes it's also true, just with a different message
                Err(AsciiUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "ASCII is not allowed in identifier Unicode fallback");
                }
                // A literal dot can start a mark identifier, but only if it is followed
                // by at least one another literal dot. Otherwise it is a Token::Dot and
                // we should stop scanning the (invalid) identifier.
                Err(Dot) => {
                    if self.peek() == Some('.') {
                        seen_start = true;
                        self.scan_identifier_mark('.');
                        break;
                    } else {
                        break;
                    }
                }
                // We have seen something that definitely starts some other token without seeing
                // a proper starter character for an identifier. Give up and return Unrecognized.
                // (Here decimal digits start an integer token.)
                Err(Terminator) | Err(Digit) => {
                    break;
                }
            }
        }

        if !seen_start {
            self.tok = Token::Unrecognized;
        }
    }

    /// Scan over a word identifier
    fn scan_identifier_word(&mut self, initial: char) {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, WORD_CONTINUE, MARK_START, QUOTE_START};
        use self::IdentifierSpecials::*;

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
                // The same is true for invalid Unicode escapes, just report and carry on scanning
                Err(IncorrectUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // For ASCII escapes it's also true, just with a different message
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

        self.tok = Token::Identifier;
    }

    /// Scan over a mark identifier
    fn scan_identifier_mark(&mut self, initial: char) {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, MARK_CONTINUE, QUOTE_START};
        use self::IdentifierSpecials::*;

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
                // The same is true for invalid Unicode escapes, just report and carry on scanning
                Err(IncorrectUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // For ASCII escapes it's also true, just with a different message
                Err(AsciiUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "ASCII is not allowed in identifier Unicode fallback");
                }
                // We have seen a literal dot. It is allowed in marks as long as it is followed by
                // at least one more literal dot. If that is the case, scan over all these dots.
                // Otherwise stop scanning the identifier without consuming this to-be-Token::Dot.
                Err(Dot) => {
                    if self.peek() == Some('.') {
                        while self.cur == Some('.') {
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

        self.tok = Token::Identifier;
    }

    /// Scan over a quote identifier
    fn scan_identifier_quote(&mut self, initial: char) {
        use unicode::sash_identifiers;
        use unicode::sash_identifiers::{WORD_START, MARK_START, QUOTE_START, QUOTE_CONTINUE};
        use self::IdentifierSpecials::*;

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
                // The same is true for invalid Unicode escapes, just report and carry on scanning
                Err(IncorrectUnicodeEscape) => {
                    self.report.error(Span::new(old_prev_pos, self.prev_pos),
                        "Incorrect identifier character");
                }
                // For ASCII escapes it's also true, just with a different message
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

        self.tok = Token::Identifier;
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

    // TODO: type suffixes

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

    // TODO: type suffixes

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

    // TODO: type suffixes

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
            ScannerTestSlice(r"\u{221B\u2192}\u2192\u{2192\u2192",          Token::Identifier), //
            ScannerTestSlice(" ",                                           Token::Whitespace),
            // However, if '\u' is followed by something that really does not look like a scalar
            // value, this '\u' is skipped over as if it were legal identifier constituent
            ScannerTestSlice(r"\u!",                                        Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\uguu",                                      Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u==",                                       Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice("::",                                          Token::Dualcolon),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u",                                         Token::Unrecognized),
            ScannerTestSlice("]",                                           Token::Rbrack),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\u\u{301b}",                                 Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice(r"\u\u{301b}",                                 Token::Identifier),
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
              Span::new(138, 138), Span::new(136, 138), Span::new(143, 143), Span::new(141, 143),
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
            ScannerTestSlice(r"\u{D800}\u{DDDD}_1\u{DFFF}",                 Token::Identifier),
            ScannerTestSlice(r"+\u{DEAD}\u{D912}",                          Token::Identifier),
            ScannerTestSlice(r"\u{2985}",                                   Token::Identifier),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            ScannerTestSlice(r"\u{9999999999999}==\u{Fo fo fo!}\u{a7}",     Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // But invalid values are not start codes. For example, an entirely invalid sequence
            // will not count as an identifier. The digits that immediately follow it are a part
            // of a number, they do not count as XID_Continue which magically converts the whole
            // thing into a word identifier. The scanner never backtracks.
            ScannerTestSlice(r"\u{Some}\u{Invalid}\u{Stuff}",               Token::Unrecognized),
            ScannerTestSlice(r"123",                                        Token::Integer),
            ScannerTestSlice(r" ",                                          Token::Whitespace),
            // but they do count if one drops some valid XID_Start in between:
            ScannerTestSlice(r"\u{Some}\u{Invalid}\u{Stuff}_123",           Token::Identifier),
        ], &[ Span::new(  4,   6), Span::new(  2,   6), Span::new( 11,  19), Span::new( 11,  19),
              Span::new( 21,  35), Span::new( 21,  35), Span::new( 41,  65), Span::new( 39,  65),
              Span::new( 68,  76), Span::new( 68,  76), Span::new( 76,  84), Span::new( 76,  84),
              Span::new( 86,  94), Span::new( 86,  94), Span::new( 95, 103), Span::new( 95, 103),
              Span::new(103, 111), Span::new(103, 111), Span::new(120, 137), Span::new(120, 137),
              Span::new(141, 152), Span::new(139, 152), Span::new(161, 167), Span::new(159, 167),
              Span::new(169, 178), Span::new(167, 178), Span::new(180, 187), Span::new(178, 187),
              Span::new(193, 199), Span::new(191, 199), Span::new(201, 210), Span::new(199, 210),
              Span::new(212, 219), Span::new(210, 219),
         ], &[]);
    }

    #[test]
    fn identifier_invalid_characters_plain() {
        check(&[
            // Arbitrary Unicode character sequences are considered invalid. Peculiar cases
            // in ASCII include control codes (other than whitespace), currently unassigned
            // backtick (`), and backslashes (\) which are not immediately followed by 'u'.
            // Non-ASCII cases include usage of characters outside of identifier character set
            // (e.g., general categories like No, Sk, or C), or usage of bare identifier
            // continuation characters (without a starter character preceding them). The
            // whole hunk of such invalid characters is reported as Unrecognized
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
            ScannerTestSlice("\\x12",                                       Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\\\\",                                        Token::Unrecognized),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("`foo`",                                       Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("\u{0307}\u{09E3}\\\u{1DA61}\u{200D}",         Token::Unrecognized),
            ScannerTestSlice("1",                                           Token::Integer),
            ScannerTestSlice("\u{200C}`\u{200D}x\u{200D}y",                 Token::Identifier),
            ScannerTestSlice("\n",                                          Token::Whitespace),
            // However! The scanner tolerates invalid Unicode characters in the middle of
            // identifiers. They are still reported, but the scanning goes on afterwards
            // as if they were valid, including their usage for boundary detection.
            ScannerTestSlice("f\u{0}o",                                     Token::Identifier),
            ScannerTestSlice("+\u{E666}",                                   Token::Identifier),
            ScannerTestSlice("_`some`_\\invalid\\123",                      Token::Identifier),
            ScannerTestSlice("==\u{02DC}==",                                Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("a\u{0488}b",                                  Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("C\u{20DD}_\u{20E3}",                          Token::Identifier),
            ScannerTestSlice(" ",                                           Token::Whitespace),
            ScannerTestSlice("+\u{200D}+=\u{200D}",                         Token::Identifier),
        ], &[ Span::new(  0,   1), Span::new(  1,   2), Span::new(  2,   3), Span::new(  3,   4),
              Span::new(  4,   5), Span::new(  5,   6), Span::new(  6,   7), Span::new(  8,   9),
              Span::new(  9,  10), Span::new( 10,  11), Span::new( 11,  12), Span::new( 13,  14),
              Span::new( 14,  15), Span::new( 15,  16), Span::new( 16,  17), Span::new( 17,  19),
              Span::new( 19,  21), Span::new( 22,  24), Span::new( 24,  26), Span::new( 26,  28),
              Span::new( 29,  32), Span::new( 32,  35), Span::new( 35,  39), Span::new( 39,  43),
              Span::new( 44,  47), Span::new( 47,  50), Span::new( 50,  53), Span::new( 53,  57),
              Span::new( 57,  61), Span::new( 62,  63), Span::new( 67,  68), Span::new( 68,  69),
              Span::new( 70,  71), Span::new( 74,  75), Span::new( 76,  78), Span::new( 78,  81),
              Span::new( 81,  82), Span::new( 82,  86), Span::new( 86,  89), Span::new( 90,  93),
              Span::new( 93,  94), Span::new( 94,  97), Span::new(104, 105), Span::new(107, 110),
              Span::new(111, 112), Span::new(116, 117), Span::new(118, 119), Span::new(126, 127),
              Span::new(132, 134), Span::new(138, 140), Span::new(143, 146), Span::new(147, 150),
              Span::new(152, 155), Span::new(157, 160),
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
            ScannerTestSlice(r"_`some`_\invalid\123",                       Token::Identifier),
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
        ], &[ Span::new(  1,   9), Span::new( 11,  19), Span::new( 20,  21), Span::new( 25,  26),
              Span::new( 27,  28), Span::new( 35,  36), Span::new( 41,  49), Span::new( 53,  61),
              Span::new( 64,  72), Span::new( 73,  81), Span::new( 83,  91), Span::new( 93, 101),
              Span::new(105, 107), Span::new(103, 107), Span::new(112, 135), Span::new(110, 135),
              Span::new(139, 143), Span::new(137, 143), Span::new(137, 143), Span::new(145, 149),
              Span::new(143, 149), Span::new(143, 149), Span::new(150, 170), Span::new(150, 170),
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
        ], &[ Span::new( 1,  7), Span::new(16, 22), Span::new(26, 32), Span::new(32, 38),
              Span::new(38, 44), Span::new(45, 51), Span::new(52, 58), Span::new(60, 66),
              Span::new(72, 80), Span::new(86, 92),
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

    // TODO: boundary tests between all token types

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
