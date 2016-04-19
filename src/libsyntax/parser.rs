// Copyright (c) 2016, ilammy
//
// Licensed under MIT license (see LICENSE file in the root directory).
// This file may be copied, distributed, and modified only in accordance
// with the terms specified by this license.

//! Sash syntax analyzer.
//!
//! This module contains definition and implementation of the _syntax analyzer_ which converts
//! a stream of tokens into an expression tree.

use std::iter::Iterator;

use diagnostics::{DiagnosticBuilder, Handler, Span};
use expressions::{Expression, ExpressionKind};
use intern_pool::{InternPool};
use lexer::{Scanner, ScannedToken};
use tokens::{Token, Delimiter, Keyword};

// - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
// The parser
//

/// Sash parser.
///
/// A parser analyzes a stream of tokens to find grammatically valid patterns in it and produce
/// a parse tree of expressions denoted by the token stream.
pub struct Parser<'a, Tokens> {
    /// The token stream to parse.
    tokens: Tokens,

    /// Set to true when we have consumed everything in the stream.
    eof_reached: bool,

    /// The intern pool for atoms stored in scanned tokens.
    pool: &'a InternPool,

    // Parsing state
    //
    //     buf:
    //     +---+-----------------+--------------+
    //     | } | Keyword(Module) | Ident("foo") |
    //     +---+-----------------+--------------+
    //       ^   ^                 ^
    //       |   |                next(): lookahead token used by the parser to decide
    //       |   |                        what to expect next
    //       |   |
    //       |  cur(): the token that the parser is currently looking at
    //       |
    //      prev(): lookbehind token used by the parser mostly for error reporting
    //
    //     tokens:
    //     +---+-------------------+--------------+----
    //     | { | Keyword(Function) | Ident("bar") | ...
    //     +---+-------------------+--------------+----
    //     remaining token stream (after the lookahead)

    /// Token buffer.
    buf: [ScannedToken; 3],

    //
    // Diagnostic reporting
    //

    /// Our designated responsible for diagnostic processing.
    handler: &'a Handler,
}

type ParseResult<'a> = Result<Expression, DiagnosticBuilder<'a>>;

impl<'a, S> Parser<'a, S>
    where S: Scanner
{
    /// Create a new parser for the given token stream.
    ///
    /// The pool is expected to be the same as the one used by the scanner (i.e., the atoms found
    /// in tokens must be there or we will panic). Any syntax errors will be reported using the
    /// provided error handler.
    pub fn new(tokens: S, pool: &'a InternPool, handler: &'a Handler) -> Parser<'a, S> {
        let placeholder = ScannedToken {
            tok: Token::Eof,
            span: Span::new(0, 0),
        };
        let mut parser = Parser {
            tokens: tokens,
            eof_reached: false,
            pool: pool,
            buf: [
                placeholder.clone(),
                placeholder.clone(),
                placeholder.clone(),
            ],
            handler: handler,
        };
        parser.fill_buffer();
        return parser;
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Stream control

    /// Peek at the previous token that has been processed.
    fn prev(&self) -> &ScannedToken {
        &self.buf[0]
    }

    /// Peek at the current token being processed.
    fn cur(&self) -> &ScannedToken {
        &self.buf[1]
    }

    /// Peek at the next token to be processed.
    fn next(&self) -> &ScannedToken {
        &self.buf[2]
    }

    /// Check whether the end of token stream has been reached.
    fn at_eof(&self) -> bool {
        self.cur().tok == Token::Eof
    }

    /// Initialize the token buffer.
    fn fill_buffer(&mut self) {
        // Read in the to-be-current token and the lookahead.
        self.read();
        self.read();
    }

    /// Bump the buffer, reading in the next token.
    fn read(&mut self) {
        self.buf.swap(0, 1);
        self.buf.swap(1, 2);
        self.buf[2] = self.next_token();
    }

    /// Fetch the next significant (non-whitespace) token.
    fn next_token(&mut self) -> ScannedToken {
        loop {
            let t = self.tokens.next_token();

            match t.tok {
                Token::Comment | Token::Whitespace => {
                    continue;
                }
                _ => {
                    return t;
                }
            }
        }
    }

    /// Clear the token buffer and mark the stream as exhausted.
    fn drain(&mut self) {
        let placeholder = ScannedToken {
            tok: Token::Eof,
            span: Span::new(0, 0),
        };
        self.buf[0] = placeholder.clone();
        self.buf[1] = placeholder.clone();
        self.buf[2] = placeholder.clone();

        self.eof_reached = true;
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Parser entry points

    /// Parse the entire token stream containing one source file.
    ///
    /// Returns None if no output can be produced, either due to the token stream being empty,
    /// or due to unrecoverable parsing errors.
    pub fn parse_all(&mut self) -> Option<Expression> {
        // Return None if we have already consumed all tokens.
        if self.eof_reached {
            return None;
        }

        // Collect top-level expressions into an implicit module.
        let mut body = Vec::new();

        while !self.at_eof() {
            match self.parse_toplevel() {
                Ok(expr) => {
                    body.push(expr);
                }
                Err(mut error) => {
                    // Only fatal issues bubble up to here, so report this and get out.
                    error.report();

                    // Don't forget to drain the token stream before we leave, it's poisoned.
                    self.drain();

                    return None;
                }
            }
        }
        self.eof_reached = true;

        // If the source file is empty then return the span of Token::Eof.
        // It's not that the user should care.
        let span = if body.is_empty() {
            self.cur().span
        } else {
            let first_span = body.first().unwrap().span;
            let last_span = body.last().unwrap().span;
            Span::new(first_span.from, last_span.to)
        };

        // Wrap the top-level expressions into an implicit module.
        return Some(Expression {
            kind: ExpressionKind::ImplicitModule {
                body: body,
            },
            span: span
        });
    }

    // - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - - -
    // Top level constructs

    /// Parse a single top-level definition.
    fn parse_toplevel(&mut self) -> ParseResult<'a> {
        match self.cur().tok {
            Token::Keyword(Keyword::Module) => {
                self.parse_module()
            }
            Token::Keyword(Keyword::Library) => {
                self.parse_library()
            }
            // Skip any invalid expressions after guessing their form (block or statement).
            _ => {
                self.parse_unrecognized_block_or_statement()
            }
        }
    }

    /// Parse an invalid expression of unknown form and return Unrecognized. If the expression has
    /// an opening brace then it is treated as a block expression and will be scanned until the
    /// matching closing brace. If we see a semicolon then it must have been a statement and we
    /// stop at that point. Everything else is simply skipped over, though we still check that
    /// all delimiters are properly nested.
    fn parse_unrecognized_block_or_statement(&mut self) -> ParseResult<'a> {
        let unrecognized_start = self.cur().span.from;

        loop {
            match self.cur().tok {
                Token::Eof => {
                    let unrecognized_end = self.cur().span.to;

                    return Ok(Expression {
                        kind: ExpressionKind::Unrecognized,
                        span: Span::new(unrecognized_start, unrecognized_end),
                    });
                }
                Token::Semicolon => {
                    let unrecognized_end = self.cur().span.to;

                    self.read();

                    return Ok(Expression {
                        kind: ExpressionKind::Unrecognized,
                        span: Span::new(unrecognized_start, unrecognized_end),
                    });
                }
                Token::OpenDelim(delim) => {
                    let e = try!(self.skip_delimited_expression(delim));
                    let unrecognized_end = e.span.to;

                    if delim == Delimiter::Brace {
                        return Ok(Expression {
                            kind: ExpressionKind::Unrecognized,
                            span: Span::new(unrecognized_start, unrecognized_end),
                        });
                    }
                }
                Token::CloseDelim(_) => {
                    return Err(self.handler.prepare_fatal(self.cur().span,
                        "unmatched closing delimiter"));
                }
                _ => {
                    self.read();
                }
            }
        }
    }

    /// Skip over a subexpression delimited by `delim`. This method does not parse the expression,
    /// but it does check for unmatched delimiters: an Err is returned in this case. Otherwise it
    /// returns an Ok(Unrecognized) result.
    fn skip_delimited_expression(&mut self, delim: Delimiter) -> ParseResult<'a> {
        let expr_from = self.cur().span.from;

        // We do expect this to start with proper delimiter.
        assert!(self.cur().tok == Token::OpenDelim(delim));
        self.read();

        loop {
            match self.cur().tok {
                // If we see another opener then recurse into the subexpression. This method
                // returns only fatal errors, so bubble them up if they are encountered.
                Token::OpenDelim(open_delim) => {
                    try!(self.skip_delimited_expression(open_delim));
                }
                Token::CloseDelim(close_delim) => {
                    // If this is the delimiter we are looking for then we are done,
                    // return some dummy node.
                    if close_delim == delim {
                        let expr_to = self.cur().span.to;

                        self.read();

                        return Ok(Expression {
                            kind: ExpressionKind::Unrecognized,
                            span: Span::new(expr_from, expr_to),
                        });
                    } else {
                        // Otherwise, this is a fatal failure. Technically, we could skip this
                        // and try to continue reading, but unmatched closing delimiter may mean
                        // that _the opening one_ was incorrect and we may have erroneously skipped
                        // over the half of the source code. Don't take chances and let the human
                        // make a decision on how to fix this.
                        return Err(self.handler.prepare_fatal(self.cur().span,
                            format!("invalid closing delimiter, expected {:?}",
                                delim).as_ref()));
                    }
                }
                Token::Eof => {
                    // TODO: tell the user where matching opener is
                    return Err(self.handler.prepare_fatal(self.cur().span,
                        format!("missing closing delimiter, expected {:?}", delim).as_ref()));
                }
                _ => {
                    self.read();
                }
            }
        }
    }

    /// Parse a single module definition.
    fn parse_module(&mut self) -> ParseResult<'a> {
        // A module starts with a 'module' keyword which we have already seen.
        assert!(self.cur().tok == Token::Keyword(Keyword::Module));
        self.read();

        let module_start = self.prev().span.from;
        let name_start = self.cur().span.from;

        // Then we expect an identifier with the name of the module.
        let module_name = match self.cur().tok {
            // We're lucky if this is so. Read over it and go on.
            Token::Identifier(module_name) => {
                self.read();
                Some(module_name)
            }
            // Otherwise mark it as missing and go on.
            _ => {
                None
            }
        };

        // After a name we expect to see an opening brace.
        let atomic_name = match self.cur().tok {
            // Got it!
            Token::OpenDelim(Delimiter::Brace) => {
                self.read();
                true
            }
            // Otherwise, let's see what we can do... Apparently, the user does not know the
            // module syntax, so we start dropping tokens until we see something sensible.
            _ => {
                loop {
                    match self.cur().tok {
                        // Okay, this seems like a start of the module body so go out.
                        Token::OpenDelim(Delimiter::Brace) => {
                            self.read();
                            break;
                        }
                        // Top-level keywords are unexpected before module definition starts so
                        // assume that the 'module' keyword we've seen is a lie. Discard everything
                        // up to this point in hope that the parser will resynchronize. Closing
                        // brace may mean the end of some enclosing block (or it is unmatched and
                        // will result in a fatal error anyway).
                        Token::Keyword(Keyword::Module) | Token::Keyword(Keyword::Library) |
                        Token::CloseDelim(Delimiter::Brace) => {
                            let module_end = self.prev().span.to;

                            self.handler.error(Span::new(module_start, module_end),
                                "invalid module definition");

                            return Ok(Expression {
                                kind: ExpressionKind::Unrecognized,
                                span: Span::new(module_start, module_end),
                            });
                        }
                        // Semicolon is a definite terminator of a non-block item. The user seems
                        // to believe that a module is one while it's not. Eat the semicolon and
                        // return a dummy node. The parser should resynchronize after this.
                        Token::Semicolon => {
                            let module_end = self.cur().span.to;

                            self.handler.error(Span::new(module_start, module_end),
                                "invalid module definition");

                            self.read();

                            return Ok(Expression {
                                kind: ExpressionKind::Unrecognized,
                                span: Span::new(module_start, module_end),
                            });
                        }
                        // Delimiters other than the opening brace are totally not expected here,
                        // so we cannot assume any sane local mistake made by the user. Just skip
                        // over it, only check for unmatched delimiters, and go on if possible.
                        Token::OpenDelim(delim) => {
                            try!(self.skip_delimited_expression(delim));
                        }
                        Token::CloseDelim(_) => {
                            return Err(self.handler.prepare_fatal(self.cur().span,
                                "unmatched closing delimiter"));
                        }
                        // If there is nothing more in the stream then we can't recover.
                        Token::Eof => {
                            return Err(self.handler.prepare_fatal(self.cur().span,
                                "expected a module definition"));
                        }
                        // Skip everything else.
                        _ => {
                            self.read();
                        }
                    }
                }
                false
            }
        };

        let name_end = self.prev().span.to;

        // O-o-okay, now we're scanning the module body until we see a matching closing brace.
        let mut module_body = Vec::new();

        loop {
            match self.cur().tok {
                // We're done. Eat the brace and go out.
                Token::CloseDelim(Delimiter::Brace) => {
                    self.read();
                    break;
                }
                // Woops, the brace has just lost its twin sister :(
                Token::Eof => {
                    // TODO: tell the user which module we expect this for
                    return Err(self.handler.prepare_fatal(self.cur().span,
                        "missing closing brace '}'"));
                }
                // Otherwise, this must be some top-level definition. If it has been parsed okay
                // then store it. If the parser has failed to recover then we can't proceeed and
                // just report the error to the caller.
                _ => {
                    match self.parse_toplevel() {
                        Ok(expr) => {
                            module_body.push(expr);
                        }
                        Err(error) => {
                            return Err(error);
                        }
                    }
                }
            }
        }

        let module_end = self.prev().span.to;

        let module_name = if atomic_name && module_name.is_some() {
            module_name.unwrap()
        } else {
            // If we have invalid module name then complain about it and use some stub instead.
            self.handler.error(Span::new(name_start, name_end),
                "invalid module name");

            self.pool.intern("<invalid-name>")
        };

        // We have seen everything that has to be seen. Return the module.
        return Ok(Expression {
            kind: ExpressionKind::Module {
                name: module_name,
                body: module_body,
            },
            span: Span::new(module_start, module_end),
        });
    }

    /// Parse a single library definition.
    fn parse_library(&mut self) -> ParseResult<'a> {
        // A library starts with a 'library' keyword which we have already seen.
        assert!(self.cur().tok == Token::Keyword(Keyword::Library));
        self.read();

        let library_start = self.prev().span.from;
        let name_start = self.cur().span.from;

        // Then we expect an identifier with the name of the library.
        let library_name = match self.cur().tok {
            // We're lucky if this is so. Read over it and go on.
            Token::Identifier(library_name) => {
                self.read();
                Some(library_name)
            }
            // Otherwise mark it as missing and go on.
            _ => {
                None
            }
        };

        // After a name we expect to see an opening brace.
        let atomic_name = match self.cur().tok {
            // Got it!
            Token::OpenDelim(Delimiter::Brace) => {
                self.read();
                true
            }
            // Otherwise, let's see what we can do... Apparently, the user does not know the
            // library syntax, so we start dropping tokens until we see something sensible.
            _ => {
                loop {
                    match self.cur().tok {
                        // Okay, this seems like a start of the library body so go out.
                        Token::OpenDelim(Delimiter::Brace) => {
                            self.read();
                            break;
                        }
                        // Top-level keywords are unexpected before library definition starts so
                        // assume that the 'library' keyword we've seen is a lie. Discard all stuff
                        // up to this point in hope that the parser will resynchronize. Closing
                        // brace may mean the end of some enclosing block (or it is unmatched and
                        // will result in a fatal error anyway).
                        Token::Keyword(Keyword::Module) | Token::Keyword(Keyword::Library) |
                        Token::CloseDelim(Delimiter::Brace) => {
                            let library_end = self.prev().span.to;

                            self.handler.error(Span::new(library_start, library_end),
                                "invalid library definition");

                            return Ok(Expression {
                                kind: ExpressionKind::Unrecognized,
                                span: Span::new(library_start, library_end),
                            });
                        }
                        // Semicolon is a definite terminator of a non-block item. The user seems
                        // to believe that a library is one while it's not. Eat the semicolon and
                        // return a dummy node. The parser should resynchronize after this.
                        Token::Semicolon => {
                            let library_end = self.cur().span.to;

                            self.handler.error(Span::new(library_start, library_end),
                                "invalid library definition");

                            self.read();

                            return Ok(Expression {
                                kind: ExpressionKind::Unrecognized,
                                span: Span::new(library_start, library_end),
                            });
                        }
                        // Delimiters other than the opening brace are totally not expected here,
                        // so we cannot assume any sane local mistake made by the user. Just skip
                        // over it, only check for unmatched delimiters, and go on if possible.
                        Token::OpenDelim(delim) => {
                            try!(self.skip_delimited_expression(delim));
                        }
                        Token::CloseDelim(_) => {
                            return Err(self.handler.prepare_fatal(self.cur().span,
                                "unmatched closing delimiter"));
                        }
                        // If there is nothing more in the stream then we can't recover.
                        Token::Eof => {
                            return Err(self.handler.prepare_fatal(self.cur().span,
                                "expected a library definition"));
                        }
                        // Skip everything else.
                        _ => {
                            self.read();
                        }
                    }
                }
                false
            }
        };

        let name_end = self.prev().span.to;

        // O-o-okay, now we're scanning the library body until we see a matching closing brace.
        let mut library_body = Vec::new();

        loop {
            match self.cur().tok {
                // We're done. Eat the brace and go out.
                Token::CloseDelim(Delimiter::Brace) => {
                    self.read();
                    break;
                }
                // Woops, the brace has just lost its twin sister :(
                Token::Eof => {
                    // TODO: tell the user which library we expect this for
                    return Err(self.handler.prepare_fatal(self.cur().span,
                        "missing closing brace '}'"));
                }
                // Otherwise, this must be some top-level definition. If it has been parsed okay
                // then store it. If the parser has failed to recover then we can't proceeed and
                // just report the error to the caller.
                _ => {
                    match self.parse_toplevel() {
                        Ok(expr) => {
                            library_body.push(expr);
                        }
                        Err(error) => {
                            return Err(error);
                        }
                    }
                }
            }
        }

        let library_end = self.prev().span.to;

        let library_name = if atomic_name && library_name.is_some() {
            library_name.unwrap()
        } else {
            // If we have invalid library name then complain about it and use some stub instead.
            self.handler.error(Span::new(name_start, name_end),
                "invalid library name");

            self.pool.intern("<invalid-name>")
        };

        // We have seen everything that has to be seen. Return the library.
        return Ok(Expression {
            kind: ExpressionKind::Library {
                name: library_name,
                body: library_body,
            },
            span: Span::new(library_start, library_end),
        });
    }
}
