use std::error::Error;
use std::io::{self, Read, ErrorKind};
use std::fmt;
use std::iter::{once, repeat};
use std::collections::HashSet;
use std::str::FromStr;
use std::str;

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Opts {
    buf_size: usize,
    buf_num: usize,
    max_buf_num: usize,
    max_stream: u64,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            buf_size: 8192,
            buf_num: 3,
            max_buf_num: 3 * 2,
            max_stream: u32::MAX as u64,
        }
    }
}

// let opts = Opts::default()
//             .set_buf_num(5)
//             .set_infinite_stream();
impl Opts {
    pub fn set_buf_size(self, s: usize) -> Opts {
        Opts {
            buf_size: s,
            buf_num: self.buf_num,
            max_buf_num: self.max_buf_num,
            max_stream: self.max_stream,
        }
    }
    pub fn set_buf_num(self, s: usize) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: s,
            max_buf_num: self.max_buf_num,
            max_stream: self.max_stream,
        }
    }
    pub fn set_max_buf_num(self, s: usize) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_buf_num: s,
            max_stream: self.max_stream,
        }
    }
    pub fn set_max_stream(self, s: u64) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_buf_num: self.max_buf_num,
            max_stream: s,
        }
    }
    pub fn set_infinite_stream(self) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_buf_num: self.max_buf_num,
            max_stream: 0,
        }
    }
}

type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug)]
pub enum ParseError {
    ParseFailed(String),
    Unrecoverable(Box<ParseError>),
    IOError(io::Error)
}

impl Error for ParseError { }

impl fmt::Display for ParseError {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        match self {
            ParseError::ParseFailed(msg) => write!(f, "parsing failed: {}", msg),
            ParseError::Unrecoverable(e) => write!(f, "cannot recover from error '{}'", e),
            ParseError::IOError(e) => write!(f, "I/O error: {:?}", e),
        }
    }
}

fn err_not_impl() -> ParseError {
    ParseError::ParseFailed("not yet implemented".to_string())
}

fn err_no_input() -> ParseError {
    ParseError::ParseFailed("no input".to_string())
}

fn err_eof() -> ParseError {
    ParseError::ParseFailed("end of file".to_string())
}

fn err_not_eof() -> ParseError {
    ParseError::ParseFailed("not the end of file".to_string())
}

fn err_exceeds_buffers(needed: usize, have: usize) -> ParseError {
    ParseError::ParseFailed(format!(
       "parser needs more buffer space ({}) than available ({})", needed, have))
}

fn err_expected_byte(expected: u8, have: u8) -> ParseError {
    ParseError::ParseFailed(format!(
       "expected byte: {}, have: {}", expected, have))
}

fn err_expected_char(expected: char) -> ParseError {
    ParseError::ParseFailed(format!(
       "expected char: {}", expected))
}

fn err_expected_whitespace(have: u8) -> ParseError {
    ParseError::ParseFailed(format!(
       "expected whitespace, have: {}", have))
}

fn err_not_a_digit(have: u8) -> ParseError {
    ParseError::ParseFailed(format!(
       "ascii digit expected, have: {}", have))
}

fn err_all_failed() -> ParseError {
    ParseError::ParseFailed(format!(
       "all parsers of a choice failed"))
}

fn err_unrecoverable(e: ParseError) -> ParseError {
    ParseError::Unrecoverable(Box::new(e))
}


#[derive(Debug, Clone, Copy)]
struct Cursor {
    buf: usize,
    pos: usize,
    stream: u64,
    line: u64,
    lpos: u64,
}

pub struct Parser<R: Read> {
    reader: R,
    bufs: Vec<Buf>,
    valid: Vec<bool>,
    cur: Cursor,
    opts: Opts,
    inited: bool,
    eof: bool,
    white_space: HashSet<u8>,
    // alternatives
}

type Buf = Vec<u8>;

impl<R: Read> Parser<R> {
    pub fn new(opts: Opts, reader: R) -> Parser<R> {
       let mut buf = Vec::with_capacity(opts.buf_num);
       for i in 0..opts.buf_num {
           buf.push(vec!(0; opts.buf_size));
       }
       let mut valid = Vec::with_capacity(opts.buf_num);
       for i in 0 .. opts.buf_num {
           valid.push(false);
       }

       Parser {
          reader: reader,
          bufs: buf,
          valid: valid,
          opts: opts,
          inited: false,
          eof: false,
          white_space: HashSet::from([' ' as u8, '\n' as u8, '\t' as u8]),
          cur: Cursor {
              buf: 0,
              pos: 0,
              stream: 0,
              line: 0,
              lpos: 0,
          }
       }
    }

   fn init(&mut self) -> ParseResult<()> {
       for i in 1..self.opts.buf_num {
           self.valid[i] = false;
       }
       self.fill_buf(0)?;
       self.inited = true;
       self.valid[0] = true;
       Ok(())
    }

    pub fn buf_size(self) -> usize {
        self.opts.buf_size
    }

    pub fn buf_num(self) -> usize {
        self.opts.buf_num
    }

    pub fn max_stream(self) -> u64 {
        self.opts.max_stream
    }

    pub fn set_whitespace(&mut self, w: Vec<u8>) {
        self.white_space = HashSet::new();
        for c in w {
            self.white_space.insert(c);
        }
    }

    fn advance_this(&self, cur: &mut Cursor, n: usize) {
         cur.pos += n;
         cur.buf = if cur.pos >= self.opts.buf_size {
             let m = cur.pos / self.opts.buf_size;
             (cur.buf + m)  % self.opts.buf_num
         } else {
             cur.buf
         };
         cur.pos %= self.opts.buf_size;

         cur.stream += n as u64;
         cur.lpos += 1; // line: we need to check for line breaks in n
    }

    fn advance(&mut self, n: usize) {
         let mut cur = self.cur; 
         self.advance_this(&mut cur, n);
         self.cur.buf = cur.buf;
         self.cur.pos = cur.pos;
    }

    fn reset_cur(&mut self, cur: Cursor) {
        self.cur.buf = cur.buf;
        self.cur.pos = cur.pos;
        self.cur.stream = cur.stream;
        self.cur.line = cur.line;
        self.cur.lpos = cur.lpos;
    }

    fn resettable(&self, cur: Cursor) -> bool {
        let d = if self.cur.buf > cur.buf {
            self.cur.buf - cur.buf
        } else {
            cur.buf - self.cur.buf
        };

        d < (self.opts.buf_num - 1)
    }

    fn fill_buf(&mut self, n: usize) -> ParseResult<()> {
        // println!("filling {}", n);
        loop {
            match self.reader.read(&mut self.bufs[n]) {
                Ok(0) => {
                    self.eof = true;
                    self.bufs[n].resize(0, 0);
                },
                Ok(x) => {
                    if x < self.opts.buf_size {
                        self.bufs[n].resize(x, 0);
                    }
                },
                Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(ParseError::IOError(e)),
            };
            break;
        }
        Ok(())
    }

    fn bufs_to_fill(&self, n: usize) -> usize {
        if n > self.opts.buf_size {
            let t = n - (self.opts.buf_size - self.cur.pos);
            if t > self.opts.buf_size {
                let m = t / self.opts.buf_size;
                if t%self.opts.buf_size != 0 {
                    return m + 1
                } else {
                    return m
                }
            }
        }
        1
    }

    // advance stream position and return old settings for cur
    fn consume(&mut self, n: usize, peek: bool) -> ParseResult<Cursor> {
        // check stream position

        // initialise
        if !self.inited {
            self.init()?;
        }

        /*
        println!("next buffer: {} is valid: {}"
                 , (self.cur.buf + 1) % self.opts.buf_num
                 , self.valid[(self.cur.buf + 1) % self.opts.buf_num]
        );
        */

        if self.eof && self.cur.pos >= self.bufs[self.cur.buf].len() &&
           !self.valid[(self.cur.buf + 1) % self.opts.buf_num]
        {
            return Err(err_eof());
        }

        // fill next buffer(s) if necessary
        if self.cur.pos + n >= self.bufs[self.cur.buf].len() {
            let m = self.bufs_to_fill(n);
            if m >= self.opts.buf_num {
                return Err(err_exceeds_buffers(m, self.opts.buf_num));
            }
            for i in 0 .. m {
                let j = (self.cur.buf + i + 1)%self.opts.buf_num;
                if !self.valid[j] {
                    self.fill_buf(j)?;
                    if self.bufs[j].len() > 0 {
                       self.valid[j] = true;
                    }
                }
            }
        }

        let cur = self.cur.clone();

        self.advance(n);

        if !peek && cur.buf != self.cur.buf {
            self.valid[cur.buf] = false;
        }
         
        return Ok(cur);
    }

    fn get(&self, cur: Cursor) -> u8 {
        // println!("getting {}.{}", cur.buf, cur.pos);
        self.bufs[cur.buf][cur.pos]
    }

    // Vec is more flexible!
    fn get_many(&self, cur: Cursor, size: usize, target: &mut [u8]) {
        let mut pos = cur.pos;
        let mut buf = cur.buf;
        for i in 0..size {
            target[i] = self.bufs[buf][pos];
            pos += 1;
            if pos >= self.bufs[buf].len() {
                buf = (buf + 1) % self.opts.buf_num;
                pos = 0;
            }
        }
    }

    pub fn succeed(&mut self) -> ParseResult<()> {
        Ok(())
    }

    pub fn fail(&mut self, msg: &str) -> ParseResult<()> {
        Err(ParseError::ParseFailed(msg.to_string()))
    }

    pub fn eof(&mut self) -> ParseResult<()> {
        match self.consume(1, false) {
            Ok(cur) => {
                self.reset_cur(cur);
                return Err(err_not_eof());
            },
            Err(ParseError::ParseFailed(s)) if s == "end of file" => return Ok(()),
            Err(e) => return Err(e),
        }
    }

    pub fn byte(&mut self, ch: u8) -> ParseResult<()> {
        let cur = self.consume(1, false)?;
        if self.get(cur) != ch {
            self.reset_cur(cur);
            return Err(err_expected_byte(ch, self.get(cur)));
        }

        Ok(())
    }

    pub fn character(&mut self, ch: char) -> ParseResult<()> {
        let mut b1 = [0; 4];
        let mut b2 = [0; 4];

        let n = ch.encode_utf8(&mut b1).len();

        let cur = self.consume(n, false)?;

        self.get_many(cur, n, &mut b2);

        for i in 0..n {
            if b1[i] != b2[i] {
                self.reset_cur(cur);
                return Err(err_expected_char(ch));
            }
        }

        /* the code above is more efficient,
           but it merely looks at the byte sequence.
           There are unicode sequences that are equivalent
           though encoded differently. Should we care?

        let s = match str::from_utf8(&buf[..n]) {
            Ok(s) => s,
            Err(e) => {
                self.reset_cur(cur);
                return Err(err_expected_char(ch));
            },
        };

        let c2 = match char::from_str(s) {
            Ok(c) => c,
            Err(e) => {
                self.reset_cur(cur);
                return Err(err_expected_char(ch));
            },
        };

        if ch != c2 {
            self.reset_cur(cur);
            return Err(err_expected_char(ch));
        }

        */

        Ok(())
    }

    pub fn any_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        Ok(ch)
    }

    pub fn any_character(&mut self) -> ParseResult<char> {
        return Err(err_not_impl());
    }

    pub fn digit(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        if ch < 48 || ch > 57 {
            self.reset_cur(cur);
            return Err(err_not_a_digit(ch));
        }
        Ok(ch)
    }

    // default whitespace: ' ', '\n', '\t'
    // but can be set as Vec<u8> with set_whitespace
    pub fn whitespace(&mut self) -> ParseResult<()> {
        let mut first = true;
        loop {

            // we don't want to fail on eof if we read at least one whitespace char
            let cur = match self.consume(1, false) {
                Ok(c) => c,
                Err(ParseError::ParseFailed(s)) if !first && s == "end of file" => return Ok(()),
                Err(e) => return Err(e),
            };

            let ch = self.get(cur);

            match self.white_space.get(&ch) {
                None => {
                    self.reset_cur(cur);
                    if first {
                        return Err(err_expected_whitespace(ch));
                    }
                    break;
                },

                Some(_) => if first {
                    first = false;
                }
            }
        }

        Ok(())
    }

    pub fn peek_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, true)?;
        // println!("peeking {}.{}", cur.buf, cur.pos);
        let ch = self.get(cur);
        self.reset_cur(cur);
        Ok(ch)
    }

    pub fn peek_char(&mut self) -> ParseResult<char> {
        return Err(err_not_impl());
    }

    pub fn peek_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {
        if n / self.opts.buf_size >= self.opts.buf_num - 1 {
            return Err(err_exceeds_buffers(self.opts.buf_num, self.opts.buf_num - 1)); 
        }

        let mut cur = self.consume(n, true)?;
        let sav = cur.clone();
        let mut v = Vec::with_capacity(n);
        for i in 0 .. n {
            v.push(self.get(cur));
            self.advance_this(&mut cur, 1);
        }
        self.reset_cur(sav);
        Ok(v)
    }

    pub fn peek_chars(&mut self, n: usize) -> ParseResult<Vec<char>> {
        return Err(err_not_impl());
    }

    pub fn peek_string(&mut self, n: usize) -> ParseResult<String> {
        return Err(err_not_impl());
    }

    pub fn binary(&mut self, buf: Vec<u8>) -> ParseResult<()> {
        return Err(err_not_impl());
    }

    // all parsers try to reset the cursor,
    // so attempt does not make much sense ...
    pub fn attempt<T>(&mut self, parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>) -> ParseResult<T> {
        let cur = self.cur.clone();
        match parse(self) {
            Err(e) => {
                if self.resettable(cur) {
                    self.reset_cur(cur);
                } else {
                    return Err(err_unrecoverable(e));
                }
                return Err(e);
            },
            Ok(n) => return Ok(n),
        }
    }

    // trait object or function?
    pub fn attempt2<T>(&mut self, parse: fn(&mut Parser<R>) -> ParseResult<T>) -> ParseResult<T> {
        let cur = self.cur.clone();
        match parse(self) {
            Err(e) => {
                if self.resettable(cur) {
                   self.reset_cur(cur);
                } else {
                    return Err(err_unrecoverable(e));
                }
                return Err(e);
            },
            Ok(n) => return Ok(n),
        }
    }

    pub fn optional<T>(&mut self, parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>) -> ParseResult<Option<T>> 
    {
        let cur = self.cur.clone();
        match parse(self) {
            Ok(t) => return Ok(Some(t)),
            Err(e) => {
                if self.resettable(cur) {
                    self.reset_cur(cur);
                } else {
                    return Err(err_unrecoverable(e));
                }
                return Ok(None);
            },
        }
    }

    pub fn many<T>(&mut self, parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>) -> ParseResult<Vec<T>> 
    {
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => v.push(t),
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    pub fn many_one<T>(&mut self, parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>) -> ParseResult<Vec<T>> 
    {
        let mut first = true;
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => {
                    v.push(t);
                    first = false;
                },
                Err(e) if first => return Err(e),
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    pub fn choice<T>(&mut self, parsers: Vec<&dyn Fn(&mut Parser<R>) -> ParseResult<T>>) -> ParseResult<T> 
    {
        let cur = self.cur.clone();
        for p in parsers {
            match p(self) {
                Ok(t) => return Ok(t),
                Err(e) =>
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    },
            }
        }
        Err(err_all_failed())
    }

    pub fn between<T>(&mut self,
                      before: &dyn Fn(&mut Parser<R>) -> ParseResult<()>,
                      parse:  &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                      after:  &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<T>
    {
        before(self)?;
        let r = parse(self)?;
        after(self)?;
        Ok(r)  
    }

    pub fn until<T>(&mut self,
                    parse:   &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                    stopper: &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<Vec<T>>
    {
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match stopper(self) {
               Ok(()) => break,
               Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    let t = parse(self)?;
                    v.push(t);
               }
            }
        }
        Ok(v)
    }

    // sep_by: separated by sep, stops if sep fails, fails if parser fails
    //         but succeeds if first parser fails
    pub fn sep_by<T>(&mut self,
                    parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                    sep:   &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<Vec<T>>
    {
        let mut first = true;
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => {
                    if first {
                       first = false;
                    }
                    v.push(t);
                }
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    if first {
                        break;
                    }
                    return Err(e);
                },
            }
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    // sep_by_one: same as sep by but must parse one
    pub fn sep_by_one<T>(&mut self,
                         parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                         sep:   &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<Vec<T>>
    {
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => v.push(t),
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    return Err(e);
                },
            }
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    // end_by: separated and ended by sep, stop if parser fails, fails if sep fails
    pub fn end_by<T>(&mut self,
                    parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                    sep:   &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<Vec<T>>
    {
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => v.push(t),
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    break;
                },
            }
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    return Err(e);
                },
            }
        }
        Ok(v)
    }

    // end_by_one: same as end_by but must parse one
    pub fn end_by_one<T>(&mut self,
                         parse: &dyn Fn(&mut Parser<R>) -> ParseResult<T>,
                         sep:   &dyn Fn(&mut Parser<R>) -> ParseResult<()>) -> ParseResult<Vec<T>>
    {
        let mut first = true;
        let mut v = Vec::new();
        loop {
            let cur = self.cur.clone();
            match parse(self) {
                Ok(t) => {
                     first = false;
                     v.push(t);
                },
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    if first {
                       return Err(e);
                    }
                    break;
                },
            }
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                    } else {
                        return Err(err_unrecoverable(e));
                    }
                    return Err(e);
                },
            }
        }
        Ok(v)
    }

    // string, e.g. string("BEGIN")
    // bytes, sequence of (potentially) non-unicode bytes
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::io;
    use std::iter::{repeat};
    // use std::assert_matches::assert_matches; // waiting for this one
    
    fn tiny_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let input: Vec<u8> = repeat('@' as u8).take(32).collect();
       println!("length: {}", input.len());
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }
    
    fn tiny_digit_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let input: Vec<u8> = vec![48, 49, 50, 51, 52, 53, 54, 55, 56, 57];
       println!("length: {}", input.len());
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }

    fn tiny_u16_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let s: String = repeat('ß').take(32).collect();
       let input = s.as_bytes().to_vec();
       println!("length: {}", input.len());
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }

    fn tiny_u32_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let s: String = repeat('京').take(32).collect();
       let input = s.as_bytes().to_vec();
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }

    fn tiny_ws_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let input: Vec<u8> = repeat(' ' as u8).take(8).chain(
                            repeat('@' as u8).take(8)).chain(
                            repeat(' ' as u8).take(4)).chain(
                            once('.'   as u8)).collect();
       println!("length: {}", input.len());
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }
    
    fn tiny_sep_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let input: Vec<u8> = once('@' as u8).chain(
                            once(',' as u8)).cycle().take(32).chain(
                            once('@' as u8)).collect();
       println!("length: {}: {:?}", input.len(), input);
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }
    
    fn tiny_end_stream() -> Parser<io::Cursor<Vec<u8>>> {
       let input: Vec<u8> = once('@' as u8).chain(
                            once(',' as u8)).cycle().take(32)
                            .collect();
       println!("length: {}: {:?}", input.len(), input);
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }

    fn curly_brackets_stream() -> Parser<io::Cursor<Vec<u8>>> {
        let input = vec!['{' as u8,
                         '1' as u8,
                         '2' as u8,
                         '3' as u8,
                         '}' as u8];
       Parser::new(Opts::default()
                   .set_buf_size(8)
                   .set_buf_num(3),
                   io::Cursor::new(input),
       )
    }

    #[test]
    fn test_expected_byte() {
        assert!(match tiny_stream().byte('@' as u8) {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        })
    }

    #[test]
    fn test_unexpected_byte() {
        assert!(match tiny_stream().byte('?' as u8) {
            Ok(()) => panic!("unexpected byte accepted"),
            Err(e) => match e {
                           ParseError::ParseFailed(s) =>
                               match s.strip_prefix("expected byte:") {
                                 Some(_) => true,
                                 _       => panic!("unexpected error: {}", s),
                               },
                           _ => panic!("unexpected error: {:?}", e),
                      },
        })
    }

    #[test]
    fn test_32_expected_bytes() {
        let mut s = tiny_stream();
        for _ in 0..32 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            })
        }
    }

    #[test]
    fn test_33_expected_bytes() {
        let mut s = tiny_stream();
        for i in 0..33 {
            assert!(match s.byte('@' as u8) {
                Ok(()) if i == 32 => panic!("1 byte too many!"),
                Ok(()) => continue,
                Err(e) if i == 32  => match e {
                               ParseError::ParseFailed(s) if s == "end of file" => true,
                               _ => panic!("unexpected error: {:?}", e),
                          },
                Err(e) => panic!("unexpected error: {:?} at {}", e, i),
            })
        }
    }

    #[test]
    fn test_expected_char() {
        assert!(match tiny_stream().character('@') {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        })
    }

    #[test]
    fn test_expected_u16_char() {
        assert!(match tiny_u16_stream().character('ß') {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        })
    }

    #[test]
    fn test_unexpected_u16_char() {
        assert!(match tiny_u16_stream().character('ö') {
            Ok(()) => panic!("unexpected char accepted"),
            Err(e) => match e {
                           ParseError::ParseFailed(s) =>
                               match s.strip_prefix("expected char:") {
                                 Some(_) => true,
                                 _       => panic!("unexpected error: {}", s),
                               },
                           _ => panic!("unexpected error: {:?}", e),
                      },
        })
    }

    #[test]
    fn test_32_expected_chars() {
        let mut s = tiny_u16_stream();
        for _ in 0..32 {
            assert!(match s.character('ß') {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            })
        }
    }

    #[test]
    fn test_33_expected_chars() {
        let mut s = tiny_u16_stream();
        for i in 0..33 {
            assert!(match s.character('ß') {
                Ok(()) if i == 32 => panic!("1 char too many!"),
                Ok(()) => continue,
                Err(e) if i == 32  => match e {
                               ParseError::ParseFailed(s) if s == "end of file" => true,
                               _ => panic!("unexpected error: {:?}", e),
                          },
                Err(e) => panic!("unexpected error: {:?} at {}", e, i),
            })
        }
    }

    #[test]
    fn test_expected_u32_char() {
        assert!(match tiny_u32_stream().character('京') {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        })
    }

    #[test]
    fn test_unexpected_u32_char() {
        assert!(match tiny_u32_stream().character('中') {
            Ok(()) => panic!("unexpected char accepted"),
            Err(e) => match e {
                           ParseError::ParseFailed(s) =>
                               match s.strip_prefix("expected char:") {
                                 Some(_) => true,
                                 _       => panic!("unexpected error: {}", s),
                               },
                           _ => panic!("unexpected error: {:?}", e),
                      },
        })
    }

    #[test]
    fn test_32_expected_u32_chars() {
        let mut s = tiny_u32_stream();
        for i in 0..32 {
            assert!(match s.character('京') {
                Ok(()) => true,
                Err(e) => panic!("error: {:?} at {}", e, i),
            })
        }
    }

    #[test]
    fn test_33_expected_u32_char() {
        let mut s = tiny_u32_stream();
        for i in 0..33 {
            assert!(match s.character('京') {
                Ok(()) if i == 32 => panic!("1 byte too many!"),
                Ok(()) => continue,
                Err(e) if i == 32  => match e {
                               ParseError::ParseFailed(s) if s == "end of file" => true,
                               _ => panic!("unexpected error: {:?}", e),
                          },
                Err(e) => panic!("unexpected error: {:?} at {}", e, i),
            })
        }
    }

    #[test]
    fn test_whitespace() {
        let mut s = tiny_ws_stream();
        
        assert!(match s.whitespace() {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });

        for _ in 0 .. 8 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }
        
        assert!(match s.whitespace() {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });

        assert!(match s.byte('.' as u8) {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_my_whitespace() {
        let mut s = tiny_stream();
        s.set_whitespace(vec![' ' as u8, '\n' as u8, '@' as u8]);
        assert!(match s.whitespace() {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });

        assert!(match s.whitespace() {
            Err(ParseError::ParseFailed(s)) if s == "end of file" => true,
            Ok(()) => panic!("Ok but 'end of file' expected"),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_fail() {
        assert!(match tiny_stream().fail("we are failing deliberately") {
            Err(ParseError::ParseFailed(s)) if s == "we are failing deliberately" => true,
            Err(e) => panic!("unexpected error: {:?}", e),
            Ok(_) => panic!("not failing on fail"),
        });
    }

    #[test]
    fn test_succeed() {
        assert!(match tiny_stream().succeed() {
            Ok(_) => true,
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_any_byte() {
        assert!(match tiny_stream().any_byte() {
            Ok(64) => true, // 64 = @
            Ok(ch) => panic!("unexpected byte: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_many_bytes() {
        let mut s = tiny_stream();
        for _ in 0 .. 32 {
            assert!(match s.any_byte() {
                Ok(64) => true, // 64 = @
                Ok(ch) => panic!("unexpected byte: {}", ch),
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.any_byte() {
            Err(ParseError::ParseFailed(s)) if s == "end of file" => true,
            Ok(ch) => panic!("OK but eof expected: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_peek_byte() {
        let mut s = tiny_stream();
        for _ in 0 .. 32 {
            assert!(match s.peek_byte() {
                Ok(64) => true, // 64 = @
                Ok(ch) => panic!("unexpected byte: {}", ch),
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.peek_byte() {
            Ok(64) => true, // 64 = @
            Ok(ch) => panic!("unexpected byte: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });

        for i in 0 .. 32 {
            println!("{}", i);
            assert!(match s.peek_byte() {
                Ok(64) => true, // 64 = @
                Ok(ch) => panic!("unexpected byte: {}", ch),
                Err(e) => panic!("error: {:?}", e),
            });

            assert!(match s.byte('@' as u8) {
                Ok(()) => true, // 64 = @
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.peek_byte() {
            Err(ParseError::ParseFailed(s)) if s == "end of file" => true,
            Ok(ch) => panic!("OK but eof expected: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });

        assert!(match s.any_byte() {
            Err(ParseError::ParseFailed(s)) if s == "end of file" => true,
            Ok(ch) => panic!("OK but eof expected: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_peek_bytes() {
        let mut s = tiny_stream();
        for _ in 0 .. 32 {
            assert!(match s.peek_bytes(4) {
                Ok(v) if v.len() == 4 => true,
                Ok(_) => panic!("unexpected result"),
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.peek_bytes(4) {
            Ok(v) if v.len() == 4 => true,
            Ok(_) => panic!("unexpected result"),
            Err(e) => panic!("error: {:?}", e),
        });

        for _ in 0 .. 8 {
            assert!(match s.peek_bytes(4) {
                Ok(v) if v.len() == 4 => true,
                Ok(_) => panic!("unexpected result"),
                Err(e) => panic!("error: {:?}", e),
            });

            assert!(match s.any_byte() {
                Ok(_) => true,
                Err(e) => panic!("error: {:?}", e),
            });

            assert!(match s.any_byte() {
                Ok(_) => true,
                Err(e) => panic!("error: {:?}", e),
            });

            assert!(match s.any_byte() {
                Ok(_) => true,
                Err(e) => panic!("error: {:?}", e),
            });

            assert!(match s.any_byte() {
                Ok(_) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.peek_bytes(4) {
            Ok(_) => panic!("Ok, but eof expected"),
            Err(ParseError::ParseFailed(s)) if s == "end of file" => true,
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_peek_too_many_bytes() {
        let mut s = tiny_stream();
        assert!(match s.peek_bytes(15) {
            Ok(v) if v.len() == 15 => true,
            Ok(_) => panic!("unexpected result"),
            Err(e) => panic!("error: {:?}", e),
        });
        assert!(match s.peek_bytes(16) {
            Ok(_) => panic!("unexpected result"),
            Err(ParseError::ParseFailed(s)) => 
                match s.strip_prefix("parser needs more buffer space") {
                   Some(_) => true,
                   _ => panic!("unexpected error: {}", s),
                },
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_digit() {
        let mut s = tiny_digit_stream();
        for i in 0 .. 10 {
            assert!(match s.digit() {
                Ok(n) => n == i + 48, 
                Err(e) => panic!("unexpected error: {}", e),
            });
        }
        let mut w = tiny_ws_stream();
        assert!(match w.digit() {
                Ok(n) => panic!("OK without digit in stream: {}", n),
                Err(ParseError::ParseFailed(x)) =>
                    match x.strip_prefix("ascii digit expected") {
                        Some(_) => true,
                        _       => panic!("unexpected error: {}", x),
                    },
                Err(e) => panic!("unexpected error: {}", e),
        });
    }

    #[test]
    fn test_eof() {
        let mut s = tiny_stream();
        for _ in 0..32 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }
        assert!(match s.eof() {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });
    }

    #[test]
    fn test_attempt_digit() {
        let mut t = tiny_stream();
        let parse = |s: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<u8> { s.digit() };
        assert!(match t.attempt(&parse) {
            Ok(_) => panic!("OK without digit in stream"),
            Err(ParseError::ParseFailed(x)) =>
                match x.strip_prefix("ascii digit expected") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", x),
            },
            Err(e) => panic!("unexpected error: {}", e),
        });

        // attempt did not consume anything
        for _ in 0..32 {
            assert!(match t.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }
    }

    #[test]
    fn test_attempt2_digit() {
        let mut t = tiny_stream();
        fn parse(p: &mut Parser<io::Cursor<Vec<u8>>>) -> ParseResult<u8> {
            p.digit()
        }
        // let parse = |s| { s.digit() };
        assert!(match t.attempt2(parse) {
            Ok(_) => panic!("OK without digit in stream"),
            Err(ParseError::ParseFailed(x)) =>
                match x.strip_prefix("ascii digit expected") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", x),
            },
            Err(e) => panic!("unexpected error: {}", e),
        });
    }

    #[test]
    fn test_attempt_vec() {
        let mut t = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<usize>> {
            let mut v = Vec::with_capacity(32);
            for i in 0 .. 32 {
                p.byte('@' as u8)?;
                v.push(i);
            }
            Ok(v)
        };
        assert!(match t.attempt(&parse) {
            Ok(v) if v.len() == 32 => true,
            Ok(v) => panic!("unexpected vector length: {}", v.len()),
            Err(e) => panic!("unexpected error: {}", e),
        });
    }

    #[test]
    fn test_curly_brackets() {
        let mut s = curly_brackets_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<(u8,u8,u8)> {
            let a = p.digit()?;
            let b = p.digit()?;
            let c = p.digit()?;
            Ok((a,b,c))
        };
        let before = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('{' as u8) };
        let after  = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('}' as u8) };

        assert!(match s.between(&before, &parse, &after) {
            Ok((49, 50, 51)) => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_many() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        assert!(match s.many(&parse) {
            Ok(v) if v.len() == 32 => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    } 

    #[test]
    fn test_many_0() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('o' as u8) };
        assert!(match s.many(&parse) {
            Ok(v) if v.len() == 0 => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });

        // many did not consume anything
        for _ in 0..32 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }
    } 

    #[test]
    fn test_many_one() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        assert!(match s.many_one(&parse) {
            Ok(v) if v.len() == 32 => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    } 

    #[test]
    fn test_many_one_0() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('o' as u8) };
        assert!(match s.many_one(&parse) {
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(ParseError::ParseFailed(e)) =>
                match e.strip_prefix("expected byte:") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", e),
                },
            Err(e) => panic!("unexpected error: {:?}", e),
        });

        // many did not consume anything
        for _ in 0..32 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }
    } 

    #[test]
    fn test_until() {
        let mut s = curly_brackets_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
            p.any_byte()
        };
        let stop = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
            p.byte('}' as u8)
        };
        assert!(match s.until(&parse, &stop) {
            Ok(v) if v.len() == 4 => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_optional() {
        let mut s = tiny_stream();
        let parse_ok = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let parse_fail = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('o' as u8) };

        assert!(match s.optional(&parse_ok) {
            Ok(Some(_)) => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });

        assert!(match s.optional(&parse_fail) {
            Ok(None) => true,
            Ok(n) => panic!("unexpected value: {:?}", n),
            Err(e) => panic!("unexpected error: {:?}", e),
        });

        // optional did consume one byte
        for _ in 0..31 {
            assert!(match s.byte('@' as u8) {
                Ok(()) => true,
                Err(e) => panic!("error: {:?}", e),
            });
        }

        assert!(match s.eof() {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        });
    } 

    #[test]
    fn test_sep_by() {
        let mut s = tiny_sep_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by(&parse, &sep) {
            Ok(v) if v.len() == 17 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_sep_by_1() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by(&parse, &sep) {
            Ok(v) if v.len() == 1 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_sep_by_0() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('0' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by(&parse, &sep) {
            Ok(v) if v.len() == 0 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_sep_by_one() {
        let mut s = tiny_sep_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by_one(&parse, &sep) {
            Ok(v) if v.len() == 17 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_sep_by_one_1() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by(&parse, &sep) {
            Ok(v) if v.len() == 1 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_sep_by_one_0() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('0' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.sep_by_one(&parse, &sep) {
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(ParseError::ParseFailed(s)) => 
                match s.strip_prefix("expected byte:") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", s),
            },
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_end_by() {
        let mut s = tiny_end_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.end_by(&parse, &sep) {
            Ok(v) if v.len() == 16 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_no_end() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('@' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.end_by(&parse, &sep) {
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(ParseError::ParseFailed(s)) => 
                match s.strip_prefix("expected byte:") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", s),
            },
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_end_by_0() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('o' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.end_by(&parse, &sep) {
            Ok(v) if v.len() == 0 => true,
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }

    #[test]
    fn test_end_by_one() {
        let mut s = tiny_stream();
        let parse = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte('o' as u8) };
        let sep   = |p: &mut Parser<io::Cursor<Vec<u8>>>| -> ParseResult<()> { p.byte(',' as u8) };

        assert!(match s.end_by_one(&parse, &sep) {
            Ok(v) => panic!("unexpected value: {:?}", v),
            Err(ParseError::ParseFailed(s)) => 
                match s.strip_prefix("expected byte:") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", s),
            },
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }
}
