use std::io::{self};
use std::error::Error;
use std::fmt;
use super::Cursor;

#[derive(Debug)]
pub enum ParseError {
    Failed(String, Cursor),
    Fatal(Box<ParseError>),
    Effect(String, Cursor, Vec<Box<ParseError>>),
    IOError(io::Error)
}

impl Error for ParseError { }

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        match self {
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

    pub fn is_parse_error(&self) -> bool {
        match self {
            ParseError::Failed(_, _) => true,
            _ => false,
        }
    }

    pub fn is_io_error(&self) -> bool {
        match self {
            ParseError::IOError(_) => true,
            _ => false,
        }
    }

    pub fn is_fatal(&self) -> bool {
        match self {
            ParseError::Fatal(_) => true,
            _ => false,
        }
    }

    pub fn is_effect(&self) -> bool {
        match self {
            ParseError::Effect(_, _, _) => true,
            _ => false,
        }
    }

    pub fn is_error_type(&self, pattern: &str) -> bool {
        match self {
            ParseError::Failed(x, _) => match x.strip_prefix(pattern) {
                Some(_) => return true,
                None => return false,
            },
            _ => return false,
        }
    }

    pub fn is_eof(&self) -> bool {
        match self {
            ParseError::Failed(s, _) if s == "end of file" => true,
            _ => false,
        }
    }

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

pub fn err_not_impl(c: Cursor) -> ParseError {
    ParseError::Failed("not yet implemented".to_string(), c)
}

pub fn err_eof(c: Cursor) -> ParseError {
    ParseError::Failed("end of file".to_string(), c)
}

pub fn err_not_eof(c: Cursor) -> ParseError {
    ParseError::Failed("not the end of file".to_string(), c)
}

pub fn err_exceeds_buffers(c: Cursor, needed: usize, have: usize) -> ParseError {
    ParseError::Failed(format!(
       "parser needs more buffer space ({}) than available ({})", needed, have),
       c,
    )
}

pub fn err_expected_byte(c: Cursor, expected: u8, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected byte: {}, have: {}", expected, have),
       c,
    )
}

pub fn err_expected_one_of_bytes(c: Cursor, expected: &[u8]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the bytes: {:?}", expected),
        c,
    )
}

pub fn err_expected_one_of_chars(c: Cursor, expected: &[char]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the characters: {:?}", expected),
        c,
    )
}

pub fn err_expected_one_of_strings(c: Cursor, expected: &[&str]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the strings: {:?}", expected),
        c,
    )
}

pub fn err_expected_char(c: Cursor, expected: char) -> ParseError {
    ParseError::Failed(format!(
       "expected char: {}", expected),
        c,
    )
}

pub fn err_expected_whitespace(c: Cursor, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected whitespace, have: {}", have),
        c,
    )
}

pub fn err_not_a_digit(c: Cursor, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected ascii digit, have: {}", have),
        c,
    )
}

pub fn err_utf8_error(c: Cursor, have: Vec<u8>) -> ParseError {
    ParseError::Failed(format!("utf8 encoding error in '{:?}'", have),
        c,
    )
}

pub fn err_expected_string(c: Cursor, expected: &str) -> ParseError {
    ParseError::Failed(format!(
        "expected string: {}", expected),
        c,
    )
}

pub fn err_all_failed(c: Cursor, v: Vec<Box<ParseError>>) -> ParseError {
    ParseError::Effect("all parsers of a choice failed".to_string(), c, v)
}

pub fn err_fatal(e: ParseError) -> ParseError {
    ParseError::Fatal(Box::new(e))
}

