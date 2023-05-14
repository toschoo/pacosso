use std::io::{self};
use std::error::Error;
use std::fmt;

#[derive(Debug)]
pub enum ParseError {
    Failed(String),
    Fatal(Box<ParseError>),
    IOError(io::Error)
}

impl Error for ParseError { }

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        match self {
            ParseError::Failed(msg) => write!(f, "parsing failed: {}", msg),
            ParseError::Fatal(e) => write!(f, "cannot recover from error '{}'", e),
            ParseError::IOError(e) => write!(f, "I/O error: {:?}", e),
        }
    }
}

impl ParseError {

    pub fn is_parse_error(&self) -> bool {
        match self {
            ParseError::Failed(_) => true,
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

    pub fn is_error_type(&self, pattern: &str) -> bool {
        match self {
            ParseError::Failed(x) => match x.strip_prefix(pattern) {
                Some(_) => return true,
                None => return false,
            },
            _ => return false,
        }
    }

    pub fn is_eof(&self) -> bool {
        match self {
            ParseError::Failed(s) if s == "end of file" => true,
            _ => false,
        }
    }

    pub fn is_expected_token(&self) -> bool {
        match self {
            ParseError::Failed(s) =>
                match s.strip_prefix("expected") {
                  Some(_) => true,
                   _ => false,
                },
            _ => false,
        }
    }

    pub fn is_utf8_error(&self) -> bool {
        match self {
            ParseError::Failed(s) =>
                match s.strip_prefix("utf8") {
                    Some(_) => true,
                    _ => false,
                },
            _ => false,
        }
    }
}

pub fn err_not_impl() -> ParseError {
    ParseError::Failed("not yet implemented".to_string())
}

pub fn err_eof() -> ParseError {
    ParseError::Failed("end of file".to_string())
}

pub fn err_not_eof() -> ParseError {
    ParseError::Failed("not the end of file".to_string())
}

pub fn err_exceeds_buffers(needed: usize, have: usize) -> ParseError {
    ParseError::Failed(format!(
       "parser needs more buffer space ({}) than available ({})", needed, have))
}

pub fn err_expected_byte(expected: u8, have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected byte: {}, have: {}", expected, have))
}

pub fn err_expected_one_of_bytes(expected: &[u8]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the bytes: {:?}", expected))
}

pub fn err_expected_one_of_chars(expected: &[char]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the characters: {:?}", expected))
}

pub fn err_expected_one_of_strings(expected: &[&str]) -> ParseError {
    ParseError::Failed(format!(
       "expected one of the strings: {:?}", expected))
}

pub fn err_expected_char(expected: char) -> ParseError {
    ParseError::Failed(format!(
       "expected char: {}", expected))
}

pub fn err_expected_whitespace(have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected whitespace, have: {}", have))
}

pub fn err_not_a_digit(have: u8) -> ParseError {
    ParseError::Failed(format!(
       "expected ascii digit, have: {}", have))
}

pub fn err_utf8_error(have: Vec<u8>) -> ParseError {
    ParseError::Failed(format!("utf8 encoding error in '{:?}'", have))
}

pub fn err_expected_string(expected: &str) -> ParseError {
    ParseError::Failed(format!(
        "expected string: {}", expected))
}

pub fn err_all_failed() -> ParseError {
    ParseError::Failed(format!(
       "all parsers of a choice failed"))
}

pub fn err_fatal(e: ParseError) -> ParseError {
    ParseError::Fatal(Box::new(e))
}

