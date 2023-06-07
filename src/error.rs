use std::io::{self};
use std::error::Error;
use std::fmt;
use super::Cursor;

/// Defines the kind of error that occurred during parsing.
#[derive(Debug)]
pub enum ParseError {
    /// `Option` signals that the options given by the creater
    /// of the `Stream` are invalid, e.g. not enough internal buffers.
    /// This error is not related to parsing proper but to the choice of options.
    Option(String),

    /// `Failed` is an error that violates the parsing rules
    /// defined by user code, e.g. an unexpected token.
    /// `Failed` indicates the position where the error occurred.
    Failed(String, Cursor),

    /// `Fatal` wraps another kind of error, typically a `Failed`,
    /// to signal that the cursor cannot be reset to the position
    /// before the error occurred because there is not enough
    /// buffer space to hold all bytes that were consumed.
    /// This leaves the stream in an undefined state.
    /// Care must be taken to avoid such situations.
    /// If a parser fails late, after having already consumed
    /// a large part of the stream, the position may not be
    /// recoverable. Complex parsers are likely to need more
    /// buffer space than simpler onces. A trivial example is
    /// a language that uses curly brackets to start a block.
    /// It fails earlier than a language that uses ALGOL-like
    /// BEGIN and END keywords.
    Fatal(Box<ParseError>),

    /// `Effect` results from another parsing error,
    /// e.g. a `choice` fails if all its sub-parsers fail.
    /// `Effect` indicates the position where resulting the error occurred.
    Effect(String, Cursor, Vec<Box<ParseError>>),

    /// `IOError` is an error results from an IO problem
    /// reading the stream. It is not related to the parsing logic.
    IOError(io::Error)
}

impl Error for ParseError { }

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        match self {
            ParseError::Option(e) => write!(f, "invalid option: {}", e),
            ParseError::Failed(e, c) => write!(f, "parsing failed: {} at {}", e, c),
            ParseError::Fatal(e) => write!(f, "cannot recover from error '{}'", e),
            ParseError::IOError(e) => write!(f, "I/O error: {:?}", e),
            ParseError::Effect(s, c, v) => {
                write!(f, "parsing failed at {} due to previous errors '{}': ", s, c)?;
                for e in v {
                    e.fmt(f)?;
                }
                Ok(())
            },
        }
    }
}

impl ParseError {

    /// Returns true if `self` is `Failed`.
    pub fn is_parse_error(&self) -> bool {
        match self {
            ParseError::Failed(_, _) => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `IOError`.
    pub fn is_io_error(&self) -> bool {
        match self {
            ParseError::IOError(_) => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `Fatal`.
    pub fn is_fatal(&self) -> bool {
        match self {
            ParseError::Fatal(_) => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `Effect`.
    pub fn is_effect(&self) -> bool {
        match self {
            ParseError::Effect(_, _, _) => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `Option`.
    pub fn is_option(&self) -> bool {
        match self {
            ParseError::Option(_) => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `Failed`
    /// and the error message starts with `pattern`.
    pub fn is_error_type(&self, pattern: &str) -> bool {
        match self {
            ParseError::Failed(x, _) => match x.strip_prefix(pattern) {
                Some(_) => return true,
                None => return false,
            },
            _ => return false,
        }
    }

    /// Returns true if `self` is `Failed`
    /// and the error message `end of file`.
    pub fn is_eof(&self) -> bool {
        match self {
            ParseError::Failed(s, _) if s == "end of file" => true,
            _ => false,
        }
    }

    /// Returns true if `self` is `Failed`
    /// and the error message is one of
    ///
    /// * expected byte
    ///
    /// * expected char
    ///
    /// * expected string
    ///
    /// * expected one of bytes
    ///
    /// * expected one of characters
    ///
    /// * expected one of strings
    ///
    /// * expected ascii digit
    ///
    /// * expected whitespace
    ///
    pub fn is_expected_token(&self) -> bool {
        match self {
            ParseError::Failed(s, _) =>
                match s.strip_prefix("expected") {
                  Some(_) => true,
                   _ => false,
                },
            _ => false,
        }
    }

    /// Returns true if `self` is `Failed`
    /// and the error message indicates that the bytes in question
    /// do not represent a valid UTF-8 encoding.
    pub fn is_utf8_error(&self) -> bool {
        match self {
            ParseError::Failed(s, _) =>
                match s.strip_prefix("utf8") {
                    Some(_) => true,
                    _ => false,
                },
            _ => false,
        }
    }

    /// Returns true if `self` is `Effect`
    /// and the error message indicates that choice failed.
    pub fn is_choice_failed(&self) -> bool {
        match self {
            ParseError::Effect(s, _, _) =>
                match s.strip_prefix("all parsers of a choice") {
                    Some(_) => true,
                    _ => false,
                },
            _ => false,
        }
    }
}

pub(crate) fn err_eof(c: Cursor) -> ParseError {
    ParseError::Failed("end of file".to_string(), c)
}

pub(crate) fn err_not_eof(c: Cursor) -> ParseError {
    ParseError::Failed("not the end of file".to_string(), c)
}

pub(crate) fn err_exceeds_buffers(c: Cursor, needed: usize, have: usize) -> ParseError {
    ParseError::Failed(format!(
       "parser needs more buffer space ({}) than available ({})", needed, have),
       c,
    )
}

pub(crate) fn err_expected_byte(c: Cursor, expected: u8, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected byte: {}, have: {}", expected, have),
       c,
    )
}

pub(crate) fn err_expected_char(c: Cursor, expected: char, have: &[u8]) -> ParseError {
    ParseError::Failed(format!(
       "expected char: {}, have: {:?}", expected, have),
        c,
    )
}

pub(crate) fn err_expected_string(c: Cursor, expected: &str, have: &str) -> ParseError {
    ParseError::Failed(format!(
        "expected string: {}, have: {}", expected, have),
        c,
    )
}

pub(crate) fn err_expected_one_of_bytes(c: Cursor, expected: &[u8], have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the bytes: {:?}, have: {}", expected, have),
        c,
    )
}

pub(crate) fn err_expected_one_of_chars(c: Cursor, expected: &[char], have: char) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the characters: {:?}, have: {}", expected, have),
        c,
    )
}

pub(crate) fn err_expected_one_of_strings(c: Cursor, expected: &[&str]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the strings: {:?}", expected),
        c,
    )
}

pub(crate) fn err_expected_whitespace(c: Cursor, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected whitespace, have: {}", have),
        c,
    )
}

pub(crate) fn err_not_a_digit(c: Cursor, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected ascii digit, have: {}", have),
        c,
    )
}

pub(crate) fn err_utf8_error(c: Cursor, have: Vec<u8>) -> ParseError {
    ParseError::Failed(format!("utf8 encoding error in '{:?}'", have),
        c,
    )
}

pub(crate) fn err_all_failed(c: Cursor, v: Vec<Box<ParseError>>) -> ParseError {
    ParseError::Effect("all parsers of a choice failed".to_string(), c, v)
}

pub(crate) fn err_fatal(e: ParseError) -> ParseError {
    ParseError::Fatal(Box::new(e))
}

