use std::io::{Read, ErrorKind};
use std::collections::HashSet;
use std::fmt;
use std::str;

pub mod options;
pub use self::options::{Opts};

pub mod error;
pub use self::error::*;

pub type ParseResult<T> = Result<T, ParseError>;

#[derive(Debug, Clone, Copy)]
pub struct Cursor {
    buf: usize,
    pos: usize,
    pub stream: u64,
    pub line: u64,
    pub lpos: u64,
}

impl fmt::Display for Cursor {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        write!(f, "absolute position {}, line {}, position {}",
               self.stream, self.line, self.lpos)
    }
}

pub struct Stream<'a, R: Read> {
    reader: &'a mut R,
    bufs: Vec<Buf>,
    valid: Vec<bool>,
    cur: Cursor,
    opts: Opts,
    inited: bool,
    eof: bool,
    white_space: HashSet<u8>,
}

type Buf = Vec<u8>;

impl<'a, R: Read> Stream<'a, R> {
   pub fn new(opts: Opts, reader: &'a mut R) -> Stream<R> {
       let mut buf = Vec::with_capacity(opts.buf_num);
       for _ in 0..opts.buf_num {
           buf.push(vec!(0; opts.buf_size));
       }
       let mut valid = Vec::with_capacity(opts.buf_num);
       for _ in 0 .. opts.buf_num {
           valid.push(false);
       }

       Stream {
          reader: reader,
          bufs: buf,
          valid: valid,
          opts: opts,
          inited: false,
          eof: false,
          white_space: HashSet::from([b' ', b'\n', b'\r', b'\t']),
          cur: Cursor {
              buf: 0,
              pos: 0,
              stream: 0,
              line: 1,
              lpos: 1,
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

    pub fn position(&self) -> Cursor {
        self.cur.clone()
    }

    pub fn count_lines(&mut self) {
        self.cur.line += 1;
        self.cur.lpos  = 1;
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
         cur.lpos += n as u64;
    }

    fn advance(&mut self, n: usize) {
         let mut cur = self.cur; 
         self.advance_this(&mut cur, n);
         self.cur.buf = cur.buf;
         self.cur.pos = cur.pos;
         self.cur.stream = cur.stream;
         self.cur.line = cur.line;
         self.cur.lpos = cur.lpos;
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
        println!("next buffer: {} is valid: {} (eof: {}, pos: {} of {})"
                 , (self.cur.buf + 1) % self.opts.buf_num
                 , self.valid[(self.cur.buf + 1) % self.opts.buf_num]
                 , self.eof
                 , self.cur.pos
                 , self.bufs[self.cur.buf].len()
        );
        */

        let d = if self.cur.pos <= self.bufs[self.cur.buf].len() {
            self.bufs[self.cur.buf].len() - self.cur.pos
        } else {
            0
        };

        if self.eof && n > d && // self.bufs[self.cur.buf].len() - self.cur.pos &&
           !self.valid[(self.cur.buf + 1) % self.opts.buf_num]
        {
            return Err(err_eof(self.cur.clone()));
        }

        // fill next buffer(s) if necessary
        if self.cur.pos + n >= self.bufs[self.cur.buf].len() {
            let m = self.bufs_to_fill(n);
            if m >= self.opts.buf_num {
                return Err(err_exceeds_buffers(self.cur.clone(), m, self.opts.buf_num));
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

        if self.cur.pos > self.bufs[self.cur.buf].len() {
           if self.resettable(cur) {
               self.reset_cur(cur);
           }
           self.eof = true;
           return Err(err_eof(self.cur.clone()));
        }

        if !peek && cur.buf != self.cur.buf {
            self.valid[cur.buf] = false;
        }
         
        Ok(cur)
    }

    fn get(&self, cur: Cursor) -> u8 {
        self.bufs[cur.buf][cur.pos]
    }

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

    fn check_excess(&self, n: usize) -> ParseResult<()> {
        if n / self.opts.buf_size >= self.opts.buf_num - 1 {
            return Err(err_exceeds_buffers(
                       self.cur.clone(),
                       self.opts.buf_num,
                       self.opts.buf_num - 1)
            );
        }
        Ok(())
    }

    pub fn succeed(&mut self) -> ParseResult<()> {
        Ok(())
    }

    pub fn fail<T>(&mut self, msg: &str, _dummy: T) -> ParseResult<T> {
        Err(ParseError::Failed(msg.to_string(), self.cur.clone()))
    }

    pub fn eof(&mut self) -> ParseResult<()> {
        match self.consume(1, false) {
            Ok(cur) => {
                self.reset_cur(cur);
                return Err(err_not_eof(self.cur.clone()));
            },
            Err(ParseError::Failed(s, _)) if s == "end of file" => return Ok(()),
            Err(e) => return Err(e),
        }
    }

    pub fn byte(&mut self, ch: u8) -> ParseResult<()> {
        let cur = self.consume(1, false)?;
        let b = self.get(cur);
        if b != ch {
            self.reset_cur(cur);
            return Err(err_expected_byte(self.cur.clone(), ch, b));
        }

        Ok(())
    }

    pub fn one_of_bytes(&mut self, bs: &[u8]) -> ParseResult<()> {
        for b in bs {
            match self.byte(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected byte:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur.clone())),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_bytes(self.cur.clone(), bs))
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
                return Err(err_expected_char(self.cur.clone(), ch));
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
                return Err(err_expected_char(self.cur.clone(), ch));
            },
        };

        let c2 = match char::from_str(s) {
            Ok(c) => c,
            Err(e) => {
                self.reset_cur(cur);
                return Err(err_expected_char(self.cur.clone(), ch));
            },
        };

        if ch != c2 {
            self.reset_cur(cur);
            return Err(err_expected_char(self.cur.clone(), ch));
        }

        */

        Ok(())
    }

    pub fn one_of_chars(&mut self, cs: &[char]) -> ParseResult<()> {
        for c in cs {
            match self.character(*c) {
                Ok(()) => return Ok(()),
                Err(e) if e.is_expected_token() => continue,
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_chars(self.cur.clone(), cs))
    }

    pub fn any_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        Ok(ch)
    }

    pub fn any_character(&mut self) -> ParseResult<char> {
        return Err(err_not_impl(self.cur.clone()));
    }

    pub fn digit(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        if ch < 48 || ch > 57 {
            self.reset_cur(cur);
            return Err(err_not_a_digit(self.cur.clone(), ch));
        }
        Ok(ch) // should we return digits as numbers?
    }

    // digits: read while we're seeing digits
    pub fn digits(&mut self) -> ParseResult<Vec<u8>> {
        let mut first = true;
        let mut v = Vec::new();
        loop {

            // we don't want to fail on eof if we read at least one digit 
            let cur = match self.consume(1, false) {
                Ok(c) => c,
                Err(ParseError::Failed(s, _)) if !first && s == "end of file" => break,
                Err(e) => return Err(e),
            };

            let ch = self.get(cur);

            if ch < 48 || ch > 57 {
                self.reset_cur(cur);
                if first {
                    return Err(err_not_a_digit(self.cur.clone(), ch));
                }
                break;
            }

            first = false;
            v.push(ch);
        }

        Ok(v)
    }

    // default whitespace: ' ', '\n', '\t'
    // but can be set as Vec<u8> with set_whitespace
    pub fn whitespace(&mut self) -> ParseResult<()> {
        let mut first = true;
        loop {

            // we don't want to fail on eof if we read at least one whitespace char
            let cur = match self.consume(1, false) {
                Ok(c) => c,
                Err(ParseError::Failed(s, _)) if !first && s == "end of file" => return Ok(()),
                Err(e) => return Err(e),
            };

            let ch = self.get(cur);

            match self.white_space.get(&ch) {
                None => {
                    self.reset_cur(cur);
                    if first {
                        return Err(err_expected_whitespace(self.cur.clone(), ch));
                    }
                    break;
                },

                Some(_) => if first {
                    first = false;
                },
            }

            // counting linebreaks in whitespace won't work with linebreaks in strings (for instance).
            if ch == b'\n' {
                self.cur.line += 1;
                self.cur.lpos = 1;
            }
        }

        Ok(())
    }

    // like whitespace, but always succeeds
    pub fn skip_whitespace(&mut self) -> ParseResult<()> {
        let _ = self.whitespace();
        Ok(())
    }

    // string, e.g. string("BEGIN")
    pub fn string(&mut self, pattern: &str) -> ParseResult<()> {
        let v: Vec<u8> = pattern.bytes().collect();
        match self.bytes(&v[..]) {
            Ok(()) => Ok(()),
            Err(ParseError::Failed(ref s, _)) => match s.strip_prefix("expected byte") {
                Some(_) => return Err(err_expected_string(self.cur.clone(), pattern)),
                _ => return Err(ParseError::Failed(s.to_string(), self.cur.clone())),
            }
            Err(e) => return Err(e),
        }
    }

    // string_ic
    pub fn string_ic(&mut self, pattern: &str) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let cur = self.cur.clone();
        let s = self.get_string(n)?;

        if s.to_uppercase() != pattern.to_uppercase() {
            self.reset_cur(cur);
            return Err(err_expected_string(self.cur.clone(), pattern));
        }
 
        Ok(())
    }

    pub fn one_of_strings(&mut self, bs: &[&str]) -> ParseResult<()> {
        for b in bs {
            match self.string(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected string:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur.clone())),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_strings(self.cur.clone(), bs))
    }

    pub fn one_of_strings_ic(&mut self, bs: &[&str]) -> ParseResult<()> {
        for b in bs {
            match self.string_ic(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected string:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur.clone())),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_strings(self.cur.clone(), bs))
    }

    // get next n bytes as string
    pub fn get_string(&mut self, n: usize) -> ParseResult<String> {
        self.check_excess(n)?;
        let cur = self.cur.clone();
        let v = self.get_bytes(n)?;
        match str::from_utf8(&v) {
            Ok(s)  => return Ok(s.to_string()),
            Err(std::str::Utf8Error{..}) => {
                self.reset_cur(cur);
                return Err(err_utf8_error(self.cur.clone(), v));
            },
        }
    }

    // bytes, sequence of (potentially) non-unicode bytes
    pub fn bytes(&mut self, pattern: &[u8]) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let mut cur = self.cur.clone();
        let sav = cur.clone();
        self.consume(n, false)?;
        for c in pattern {
            let b = self.get(cur);
            if *c != b {
               self.reset_cur(sav);
               return Err(err_expected_byte(self.cur.clone(), *c, b));
            }
            self.advance_this(&mut cur, 1);
        }
        Ok(())
    }

    // bytes, sequence of (potentially) non-unicode bytes
    pub fn get_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;
        let mut cur = self.cur.clone();
        self.consume(n, false)?;

        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(self.get(cur)); 
            self.advance_this(&mut cur, 1);
        }
        Ok(v)
    }

    // binary object size = buf.len()
    pub fn blob(&mut self, buf: Vec<u8>) -> ParseResult<()> {
        return Err(err_not_impl(self.cur.clone()));
    }

    // get everything in the buffers out
    pub fn drain(&mut self) -> ParseResult<Vec<u8>> {
        return Err(err_not_impl(self.cur.clone()));
    }

    pub fn peek_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, true)?;
        // println!("peeking {}.{}", cur.buf, cur.pos);
        let ch = self.get(cur);
        self.reset_cur(cur);
        Ok(ch)
    }

    pub fn peek_char(&mut self) -> ParseResult<char> {
        return Err(err_not_impl(self.cur.clone()));
    }

    pub fn peek_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;

        let mut cur = self.consume(n, true)?;
        let sav = cur.clone();
        let mut v = Vec::with_capacity(n);
        for _ in 0 .. n {
            v.push(self.get(cur));
            self.advance_this(&mut cur, 1);
        }
        self.reset_cur(sav);
        Ok(v)
    }

    pub fn peek_chars(&mut self, n: usize) -> ParseResult<Vec<char>> {
        return Err(err_not_impl(self.cur.clone()));
    }

    pub fn peek_string(&mut self, n: usize) -> ParseResult<String> {
        return Err(err_not_impl(self.cur.clone()));
    }

    // trait object or function?
    pub fn optional<T, F>(&mut self, parse: F) -> ParseResult<Option<T>> 
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
    {
        let cur = self.cur.clone();
        match parse(self) {
            Ok(t) => return Ok(Some(t)),
            Err(e) => {
                if self.resettable(cur) {
                    self.reset_cur(cur);
                } else {
                    return Err(err_fatal(e));
                }
                return Ok(None);
            },
        }
    }

    pub fn many<T, F>(&mut self, parse: F) -> ParseResult<Vec<T>> 
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
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
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    pub fn many_one<T, F>(&mut self, parse: F) -> ParseResult<Vec<T>> 
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
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
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    pub fn choice<T, F>(&mut self, parsers: &[F]) -> ParseResult<T> 
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
    {
        let mut v: Vec<Box<ParseError>> = Vec::new();
        let cur = self.cur.clone();
        for p in parsers {
            match p(self) {
                Ok(t) => return Ok(t),
                Err(e) =>
                    if self.resettable(cur) {
                        self.reset_cur(cur);
                        v.push(Box::new(e));
                    } else {
                        return Err(err_fatal(e));
                    },
            }
        }
        Err(err_all_failed(self.cur.clone(), v))
    }

    pub fn between<T, F1, F2, F3>(&mut self,
                                  before: F1,
                                  parse:  F2,
                                  after:  F3) -> ParseResult<T>
         where F1: Fn(&mut Stream<R>) -> ParseResult<()>,
               F2: Fn(&mut Stream<R>) -> ParseResult<T>,
               F3: Fn(&mut Stream<R>) -> ParseResult<()>
    {
        before(self)?;
        let r = parse(self)?;
        after(self)?;
        Ok(r)  
    }

    pub fn until<T, F1, F2>(&mut self, parse: F1, stopper: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
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
                        return Err(err_fatal(e));
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
    pub fn sep_by<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
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
                        return Err(err_fatal(e));
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
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    // sep_by_one: same as sep by but must parse one
    pub fn sep_by_one<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
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
                        return Err(err_fatal(e));
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
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    // end_by: separated and ended by sep, stop if parser fails, fails if sep fails
    pub fn end_by<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
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
                        return Err(err_fatal(e));
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
                        return Err(err_fatal(e));
                    }
                    return Err(e);
                },
            }
        }
        Ok(v)
    }

    // end_by_one: same as end_by but must parse one
    pub fn end_by_one<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
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
                        return Err(err_fatal(e));
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
                        return Err(err_fatal(e));
                    }
                    return Err(e);
                },
            }
        }
        Ok(v)
    }
}

#[cfg(test)]
mod test;
