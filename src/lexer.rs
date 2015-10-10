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

    /// A single character
    Character,

    /// A string of characters
    String,

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

/// Character scanning context
///
/// Denotes the context in which a character or an escape sequence is scanned. It is primarily used
/// by error recovery code paths. However, there are several characters the meaning of which can be
/// context-dependent, e.g., the backslash `\` character.
enum CharacterContext {
    OfCharacter,
    OfString,
}

use self::CharacterContext::*;

impl CharacterContext {
    // Method calls just read better. Compare `context.of_string()` with `context == OfString`
    // as well as `!context.of_string()` with `context != OfString`

    /// Check whether this is `CharacterContext::OfCharacter`
    fn of_character(&self) -> bool {
        match *self { OfCharacter => true, _ => false }
    }

    /// Check whether this is `CharacterContext::OfString`
    fn of_string(&self) -> bool {
        match *self { OfString => true, _ => false }
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
            '\'' => {
                self.scan_character_literal();
            }
            '"' => {
                self.scan_string();
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

    /// Scan over a single character literal
    fn scan_character_literal(&mut self) {
        // A character literal is a single quote...
        assert!(self.cur == Some('\''));
        self.read();
        let init = self.cur;

        // ...followed by one character...
        if !self.at_eof() {
            self.scan_one_character_or_escape_sequence(OfCharacter);
        }

        match self.cur {
            // ... and then by another single quote. All's fine here.
            Some('\'') => {
                self.read();
                self.tok = Token::Character;
            }
            // The file ended prematurely
            None => {
                self.report.error(Span::new(self.start, self.prev_pos),
                    "Unexpected end of file. Expected character literal.");
                self.tok = Token::Unrecognized;
            }
            // There is no terminating quote. Okay, go on scanning presuming that the user
            // meant to type a short string literal but used single quotes for some reason.
            _ => {
                // Special case: ''
                if init == Some('\'') {
                    self.report.error(Span::new(self.start, self.prev_pos),
                        "A character literal must contain a character");
                    self.tok = Token::Character;
                    return;
                }

                let presumed_end = self.prev_pos;

                while !self.at_eof() {
                    match self.cur.unwrap() {
                        '\r' if self.peek() == Some('\n') => {
                            break;
                        }
                        '\n' | '\'' => { break; }
                         _          => { self.scan_one_character_or_escape_sequence(OfCharacter); }
                    }
                }

                match self.cur {
                    // We have found a closing quote on the same line
                    Some('\'') => {
                        self.read();
                        self.report.error(Span::new(self.start, self.prev_pos),
                            "A character literal must contain only one character");
                        self.tok = Token::Character;
                    }
                    // There were no quotes on this line, maybe the first one was an error
                    Some('\r') | Some('\n') => {
                        self.report.error(Span::new(self.start, presumed_end),
                            "Missing closing quote (').");
                        self.tok = Token::Unrecognized;
                    }
                    // The file ended prematurely
                    None => {
                        self.report.error(Span::new(self.start, presumed_end),
                            "Unexpected end of file. Expected a closing single quote.");
                        self.tok = Token::Unrecognized;
                    }
                    Some(_) => { unreachable!(); } // due to the loop above
                }
            }
        }
        // TODO: type suffix
    }

    /// Scan over a string literal
    fn scan_string(&mut self) {
        // Strings start with a double quote...
        assert!(self.cur == Some('"'));
        self.read();

        loop {
            match self.cur {
                // ...and go on until another double quote is encountered.
                Some('"') => {
                    self.read();
                    self.tok = Token::String;
                    break;
                }
                // Between the double quotes there are characters and escape sequences.
                Some(_) => {
                    self.scan_one_character_or_escape_sequence(OfString);
                }
                // It is bad when the scanner encounters the end of file when scanning a string.
                // As strings can contain _arbitrary sequences of characters_, the only thing that
                // we are sure in is the double quote. It certainly means the end of string.
                // Everything else can be (possibly incorrect) string content. That's why error
                // recovery is not great when a closing quote goes missing. We just hope that it
                // results into lots of nonsensical tokens which will make the parser to give up.
                None => {
                    self.report.error(Span::new(self.start, self.pos),
                        "Unexpected end of file. Expected end of string.");
                    self.tok = Token::Unrecognized;
                    return;
                }
            }
        }
        // TODO: type suffix
    }

    /// Scan over a single character or escape sequence in character or string literal
    fn scan_one_character_or_escape_sequence(&mut self, context: CharacterContext) {
        assert!(self.cur.is_some());

        match self.cur.unwrap() {
            // Escape sequences start with a backslash.
            // But it also may be a singular backslash in character literals.
            '\\' => {
                let p = self.peek();
                if p.is_none() {
                    // Either way, we cannot do much in this case.
                    // Unexpected EOF will be reported by the caller.
                    self.read();
                    return;
                }
                match context {
                    OfCharacter => {
                        if p == Some('\'') {
                            self.read();
                        } else {
                            self.scan_escape_sequence(OfCharacter);
                        }
                    }
                    OfString => {
                        self.scan_escape_sequence(OfString);
                    }
                }
            }
            // When scanning a character, stop at line ending. It will be handled by the caller
            '\n' => {
                if !context.of_character() {
                    self.read();
                }
            }
            '\r' if self.peek() == Some('\n') => {
                if !context.of_character() {
                    self.read();
                    self.read();
                }
            }
            // Everything else is just a single character
            _ => {
                // Bare CR characters are prohibited in Sash as they are often results of VCS
                // misconfiguration or other kind of blind automated tampering with source file
                // contents. None of the popular operating systems uses bare CRs as a line ending
                // marker, and Sash does not recognize them as such.
                if self.cur.unwrap() == '\r' {
                    self.report.error(Span::new(self.prev_pos, self.pos),
                        "Bare CR characters must be escaped");
                }
                self.read();
            }
        }
    }

    /// Scan over a single escape sequence
    fn scan_escape_sequence(&mut self, context: CharacterContext) {
        assert!(self.cur == Some('\\') && self.peek().is_some());
        self.read();

        match self.cur.unwrap() {
            '0' | 't' | 'n' | 'r' | '"' | '\\' => { self.read(); }
            'x' => { self.scan_escape_byte(); }
            'u' => { self.scan_escape_unicode(context); }
            _ => {
                match self.cur.unwrap() {
                    '\n' => {
                        let start = self.prev_pos;
                        self.read();
                        match context {
                            OfCharacter => {
                                self.report.error(Span::new(start, start),
                                    "Line continuations cannot be used in character literals");
                            }
                            OfString => {
                                self.scan_whitespace();
                            }
                        }
                    }
                    '\r' if self.peek() == Some('\n') => {
                        let start = self.prev_pos;
                        self.read();
                        self.read();
                        match context {
                            OfCharacter => {
                                self.report.error(Span::new(start, start),
                                    "Line continuations cannot be used in character literals");
                            }
                            OfString => {
                                self.scan_whitespace();
                            }
                        }
                    }
                    _ => {
                        if self.cur.unwrap() == '\r' {
                            self.report.error(Span::new(self.prev_pos, self.pos),
                                "Bare CR character");
                        }
                        let start = self.prev_pos - 1;
                        self.read();
                        self.report.error(Span::new(start, self.prev_pos),
                            "Unknown escape sequence");
                    }
                }
            }
        }
    }

    /// Scan over a single byte escape sequence
    fn scan_escape_byte(&mut self) {
        assert!(self.cur == Some('x'));
        self.read();

        let mut digits = 0;
        let digits_start = self.prev_pos;
        while !self.at_eof() {
            let c = self.cur.unwrap();
            if !StringScanner::is_digit(c, 16) {
                break;
            }
            digits += 1;
            self.read();
        }
        let digits_end = self.prev_pos;

        if digits != 2 {
            self.report.error(Span::new(digits_start, digits_end),
                "Expected two hexadecimal digits.");
        }
    }

    /// Scan over a single Unicode escape sequence
    fn scan_escape_unicode(&mut self, context: CharacterContext) {
        assert!(self.cur == Some('u'));
        self.read();

        let brace_start = self.prev_pos;

        match self.cur {
            // All is well, a Unicode scalar starts with a '{'
            Some('{') => {
                self.read();
            }
            // Stuff goes right away
            _ => {
                self.report.error(Span::new(self.prev_pos, self.prev_pos),
                    "Unicode scalar value must start with '{'");

                // We can go on with scanning in character literals, because this Unicode escape
                // *should be* the only one thing in the token. Thus we can assume that whatever
                // comes next is our sequence of hexadecimal digits (at least up to a terminating
                // character like a closing quote, a slash, or a brace).
                //
                // However, this a too bold assumption for strings: we could never see a suitable
                // terminating character (i.e., a brace, a slash, or a line ending), and we could
                // call the whole remaining part of the string an 'invalid Unicode escape' which
                // is not universally true. So we quit right now, after reporting a missing opening
                // brace. The hex digits and the closing brace (if any) will be scanned over later
                // as if they were regular characters of the string.
                //
                // TODO: be more concise
                if context.of_string() {
                    return;
                }
            }
        }

        let mut empty_braces = true;
        let mut invalid_hex = false;
        let mut missing_close = false;

        loop {
            match self.cur {
                // All is well, a Unicode scalar ends with a '}'
                Some('}') => {
                    self.read();
                    break;
                }
                // Unexpected end of file. Defer error reporting to the caller
                None => {
                    return;
                }
                // Encountered clear terminator of a Unicode escape, but have not seen '}'
                Some('\\') => {
                    missing_close = true;
                    break;
                }
                Some('\'') if context.of_character() => {
                    missing_close = true;
                    break;
                }
                Some('\"') if context.of_string() => {
                    missing_close = true;
                    break;
                }
                // Encountered a line ending. This is fatal for character literals as it's most
                // probably caused by a stray and/or missing single quote. However, for strings
                // it's just another implicit terminator of our Unicode-escapeв character.
                Some('\n') => {
                    match context {
                        OfCharacter => { return; }
                        OfString => {
                            missing_close = true;
                            break;
                        }
                    }
                }
                Some('\r') if self.peek() == Some('\n') => {
                    match context {
                        OfCharacter => { return; }
                        OfString => {
                            missing_close = true;
                            break;
                        }
                    }
                }
                // Otherwise, report anything that is not a hex digit and go on
                Some(_) => {
                    empty_braces = false;
                    let c = self.cur.unwrap();
                    if !StringScanner::is_digit(c, 16) {
                        invalid_hex = true;
                    }
                }
            }
            self.read();
        }

        let brace_end = self.prev_pos;

        if missing_close {
            self.report.error(Span::new(brace_end, brace_end),
                "Unicode scalar value must end with '}'");
        }

        if empty_braces {
            self.report.error(Span::new(brace_start, brace_end),
                "Unicode scalar value is empty");
        }

        if invalid_hex {
            self.report.error(Span::new(brace_start, brace_end),
                "Incorrect Unicode scalar value. Expected only hex digits");
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
            ScannerTestSlice(r"'\x35'",         Token::Character),  // The scanner does not really
            ScannerTestSlice(r" ",              Token::Whitespace), // care about contents. It only
            ScannerTestSlice(r"'\x1f'",         Token::Character),  // checks that a literal has
            ScannerTestSlice(r" ",              Token::Whitespace), // expected number of digits.
            ScannerTestSlice(r"'\xFF'",         Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{12}'",       Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{DEAD}'",     Token::Character),  // It also does not care about
            ScannerTestSlice(r" ",              Token::Whitespace), // Unicode surrogates...
            ScannerTestSlice(r"'\u{fffff}'",    Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{99999999}'", Token::Character),  // or any Unicode range at all.
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{0}'",        Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace),
            ScannerTestSlice(r"'\u{00000005}'", Token::Character),
            ScannerTestSlice(r" ",              Token::Whitespace), // Really.
            ScannerTestSlice(r"'\u{f0f0f0deadbeef00012345}'", Token::Character),
        ], &[], &[]);
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
        ], &[ Span::new(0, 2), Span::new(20, 22), Span::new(29, 31), Span::new(39, 40),
              Span::new(34, 45), Span::new(53, 54), Span::new(45, 47) ], &[]);
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
        check(&[ ScannerTestSlice("'\\u{",  Token::Unrecognized) ], &[ Span::new(0, 4) ], &[]);
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
        ], &[ Span::new( 7,  7), Span::new(13, 13), Span::new(12, 13), Span::new(18, 24),
              Span::new(34, 34), Span::new(29, 34), Span::new(39, 57), Span::new(79, 79),
              Span::new(62, 79), Span::new(81, 97), Span::new(98, 114) ], &[]);
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
        ], &[ Span::new( 3,  3), Span::new( 3,  3), Span::new( 3,  3), Span::new( 8,  8),
              Span::new( 8,  9), Span::new(14, 14), Span::new(18, 18), Span::new(14, 18),
              Span::new(23, 23), Span::new(24, 24), Span::new(23, 24), Span::new(26, 26),
              Span::new(27, 27), Span::new(26, 27), Span::new(20, 28)
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
            ScannerTestSlice("'\\\n'",      Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("'\\\r\n'",    Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("'\\\r'",      Token::Character),
            ScannerTestSlice(" ",           Token::Whitespace),
            ScannerTestSlice("'\\\n\t!!!'", Token::Character),
        ], &[ Span::new( 1,  3), Span::new( 6,  8), Span::new(11, 13), Span::new(16, 18),
              Span::new(21, 23), Span::new(26, 28), Span::new(25, 30), Span::new(32, 34),
              Span::new(37, 40), Span::new(43, 45), Span::new(42, 47), Span::new(50, 50),
              Span::new(55, 55), Span::new(61, 62), Span::new(60, 62), Span::new(66, 66),
              Span::new(64, 72),
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
            // ...and, as with characters, do not care about their semantics.
            ScannerTestSlice(r#""\xFF\xFE\x00\xDE\xAD""#,    Token::String),
            ScannerTestSlice(r#""\u{D900}\u{F0F0F090909}""#, Token::String),
        ], &[], &[]);
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
        check(&[ ScannerTestSlice("\"\\u{",  Token::Unrecognized) ], &[ Span::new(0, 4) ], &[]);
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
        ], &[ Span::new(  7,   7), Span::new( 13,  13), Span::new( 12,  13), Span::new( 18,  24),
              Span::new( 34,  34), Span::new( 29,  34), Span::new( 39,  57), Span::new( 79,  79),
              Span::new( 62,  79), Span::new( 97,  97), Span::new( 84,  97), Span::new(137, 137),
              Span::new(124, 137), Span::new(158, 184), Span::new(199, 199), Span::new(189, 199),
              Span::new(222, 222), Span::new(212, 222), Span::new(242, 242), Span::new(234, 242),
              Span::new(242, 244), Span::new(246, 263),
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
        ], &[ Span::new(3, 3), Span::new(8, 8), Span::new(14, 14), Span::new(23, 23),
              Span::new(26, 26) ], &[]);
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
