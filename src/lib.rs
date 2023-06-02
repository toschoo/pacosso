use std::io::{self, Read, ErrorKind};
use std::ffi::OsString;
use std::fs::File;
use std::collections::HashSet;
use std::fmt;
use std::str;

pub mod options;
pub use self::options::{Opts};

pub mod error;
pub use self::error::*;

pub type ParseResult<T> = Result<T, ParseError>;
pub type ParseChain<'a, R> = ParseResult<io::Chain<io::Cursor<Vec<u8>>, &'a mut R>>;

#[derive(Debug, Clone, Copy)]
pub struct Cursor {
    buf: usize,
    pos: usize,
    pub stream: u64,
    pub line: u64,
    pub lpos: u64,
}

#[derive(Debug, Clone, Copy)]
struct BufState {
    valid: bool,
    size: usize,
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
    states: Vec<BufState>,
    cur: Cursor,
    opts: Opts,
    inited: bool,
    white_space: HashSet<u8>,
}

type Buf = Vec<u8>;

pub fn parse_file<F, T>(f: OsString, opts: Opts, parse: F) -> ParseResult<T> 
         where F: Fn(&mut Stream<File>) -> ParseResult<T>
{
    match File::open(f) {
        Ok(mut input) => {
            let mut s = Stream::new(opts, &mut input);
            return parse(&mut s);
        },
        Err(e) => return Err(ParseError::IOError(e)),
    }
}

pub fn parse_string<F, T>(s: String, opts: Opts, parse: F) -> ParseResult<T> 
         where F: Fn(&mut Stream<io::Cursor<Vec<u8>>>) -> ParseResult<T>
{
    let mut input = io::Cursor::new(s.as_bytes().to_vec());
    let mut p = Stream::new(opts, &mut input);
    parse(&mut p)
}

impl<'a, R: Read> Stream<'a, R> {
   pub fn new(opts: Opts, reader: &'a mut R) -> Stream<R> {
       let mut buf = Vec::with_capacity(opts.buf_num);
       for _ in 0..opts.buf_num {
           buf.push(vec!(0; opts.buf_size));
       }
       let mut states = Vec::with_capacity(opts.buf_num);
       for _ in 0 .. opts.buf_num {
           states.push(BufState {
               valid: false,
               size: opts.buf_size,
           });
       }

       Stream {
          reader: reader,
          bufs: buf,
          states: states,
          opts: opts,
          inited: false,
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
           self.states[i].valid = false;
           self.states[i].size  = self.opts.buf_size;
       }
       self.cur.line = 0;
       self.cur.lpos = 0;
       self.cur.buf = 0;
       self.cur.pos = 0;
       self.fill_buf(0, 0)?;
       if self.states[0].size > 0 {
           self.states[0].valid = true;
       }
       self.inited = true;
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
        self.cur
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

        // the current buffer is always valid!
        self.states[cur.buf].valid = true;
    }

    fn resettable(&self, cur: Cursor) -> bool {
        let d = if self.cur.buf > cur.buf {
            self.cur.buf - cur.buf
        } else {
            cur.buf - self.cur.buf
        };

        d < (self.opts.buf_num - 1)
    }

    fn fill_buf(&mut self, n: usize, wanted: usize) -> ParseResult<()> {
        let mut s = if self.states[n].size < self.opts.buf_size {
            self.states[n].size
        } else {
            0
        };
        let buf = &mut self.bufs[n][..];
        loop {
            match self.reader.read(&mut buf[s..]) {
                Ok(0) => {
                    self.states[n].size = s;
                },
                Ok(x) => {
                    s += x;
                    self.states[n].size = s; // redundant
                    if s < self.opts.buf_size {
                       if !self.opts.is_stream {
                           continue;
                       } else if s < wanted {
                           continue;
                       }
                    }
                },
                Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(ParseError::IOError(e)),
            };
            break;
        }
        Ok(())
    }

    fn bytes_to_read(&self, buf: usize, n: usize) -> usize {
        if self.states[buf].size == self.opts.buf_size {
           if n > self.opts.buf_size {
               return self.opts.buf_size;
           } else {
               return n;
           }
        } else {
            if n > self.opts.buf_size - self.states[buf].size {
                return self.opts.buf_size - self.states[buf].size;
            } else {
                return n;
            }
        }
    }

    // advance stream position and return old settings for cur
    fn consume(&mut self, n: usize, peek: bool) -> ParseResult<Cursor> {
        // check stream position

        // initialise
        if !self.inited {
            self.init()?;
        }

        // fill next buffer(s) if necessary
        if self.cur.pos + n >= self.states[self.cur.buf].size {
            let mut r = n; // what remains to be read

            // pre-check if we have enough room to store the request
            if n >= self.opts.buf_num * self.opts.buf_size - self.opts.buf_size {
                return Err(err_exceeds_buffers(self.cur, n/self.opts.buf_num, self.opts.buf_num));
            }

            // we only fill the current buffer if it is not completely filled
            let offset = if self.states[self.cur.buf].size == self.opts.buf_size {
                1
            } else {
                0
            };

            for i in 0 .. self.opts.buf_num {

                // we are now looking at this buffer
                let j = (self.cur.buf + i + offset)%self.opts.buf_num;

                // a socket must wait for the number of bytes we need to make progress
                // but we must not oblige it to read more than that
                let wanted = if self.opts.is_stream {
                    self.bytes_to_read(j, r)
                } else {
                    0
                };

                // we only fill incomplete or invalid buffers
                if self.states[j].size < self.opts.buf_size || !self.states[j].valid {

                    // remember the size of the buffer we have now
                    let d = if self.states[j].valid {
                        self.states[j].size
                    } else {
                        0
                    };

                    self.fill_buf(j, wanted)?;

                    // if we have read something, the buf is now valid
                    // reduce the remainder by the amount we read
                    if self.states[j].size > 0 {
                       self.states[j].valid = true;
                       if r > self.states[j].size - d {
                           r -= self.states[j].size - d;
                       } else {
                           r = 0;
                       }
                    }
                }

                // we have read enough to make progress
                if r == 0 {
                    break;
                }
            }
        }

        let cur = self.cur;

        self.advance(n);

        // if the cursor points beyond of what we read, we reached the end of the stream
        if self.cur.pos > self.states[self.cur.buf].size {
           if self.resettable(cur) {
               self.reset_cur(cur);
           }
           
           return Err(err_eof(self.cur));
        }

        // invalidate the current buffer when we leave it
        if cur.buf != self.cur.buf {
            self.states[cur.buf].valid = false;
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
            if pos >= self.states[buf].size {
                buf = (buf + 1) % self.opts.buf_num;
                pos = 0;
            }
        }
    }

    fn check_excess(&self, n: usize) -> ParseResult<()> {
        if n / self.opts.buf_size >= self.opts.buf_num - 1 {
            return Err(err_exceeds_buffers(
                       self.cur,
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
        Err(ParseError::Failed(msg.to_string(), self.cur))
    }

    pub fn eof(&mut self) -> ParseResult<()> {
        match self.consume(1, false) {
            Ok(cur) => {
                self.reset_cur(cur);
                return Err(err_not_eof(self.cur));
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
            return Err(err_expected_byte(self.cur, ch, b));
        }

        Ok(())
    }

    pub fn one_of_bytes(&mut self, bs: &[u8]) -> ParseResult<()> {
        for b in bs {
            match self.byte(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected byte:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur)),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_bytes(self.cur, bs))
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
                return Err(err_expected_char(self.cur, ch));
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
                return Err(err_expected_char(self.cur, ch));
            },
        };

        let c2 = match char::from_str(s) {
            Ok(c) => c,
            Err(e) => {
                self.reset_cur(cur);
                return Err(err_expected_char(self.cur, ch));
            },
        };

        if ch != c2 {
            self.reset_cur(cur);
            return Err(err_expected_char(self.cur, ch));
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
        Err(err_expected_one_of_chars(self.cur, cs))
    }

    pub fn any_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        Ok(ch)
    }

    fn len_of_char(&self, b: u8) -> usize {
        if b & (1 << 7) == 0 {
           return 1;
        }
        if b & (1 << 6) == 0 {
           return 0;
        }
        if b & (1 << 5) == 0 {
           return 2;
        }
        if b & (1 << 4) == 0 {
           return 3;
        }
        if b & (1 << 3) == 0 {
           return 4;
        }
        0
    }

    pub fn any_character(&mut self) -> ParseResult<char> {
        let mut bs = [0; 4];

        let cur = self.consume(1, false)?;
        let sav = cur;
        bs[0] = self.get(cur);
        let n = self.len_of_char(bs[0]);
        if n == 0 {
            self.reset_cur(cur);
            return Err(err_utf8_error(cur, bs.to_vec()));
        }
        if n == 1 {
           return Ok(bs[0] as char);
        }
        for i in 0 .. (n-1) {
            let cur = match self.consume(1, false) {
                Ok(cur) => cur,
                Err(_) => {
                    self.reset_cur(sav);
                    return Err(err_utf8_error(cur, bs.to_vec()));
                },
            };
            bs[i+1] = self.get(cur);
        }
        match str::from_utf8(&bs) {
            Ok(x) => {
                return Ok(x.chars().collect::<Vec<char>>()[0]);
            },
            Err(_) => {
                if self.resettable(sav) {
                    self.reset_cur(sav);
                }
                return Err(err_utf8_error(cur, bs.to_vec()));
            },
        }
    }

    pub fn digit(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, false)?;
        let ch = self.get(cur);
        if ch < 48 || ch > 57 {
            self.reset_cur(cur);
            return Err(err_not_a_digit(self.cur, ch));
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
                    return Err(err_not_a_digit(self.cur, ch));
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
                        return Err(err_expected_whitespace(self.cur, ch));
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
                Some(_) => {
                    return Err(err_expected_string(self.cur, pattern));
                },
                _ => Err(ParseError::Failed(s.to_string(), self.cur)),
            }
            Err(e) => Err(e),
        }
    }

    // string_ic
    pub fn string_ic(&mut self, pattern: &str) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let cur = self.cur;
        let s = self.get_string(n)?;

        if s.to_uppercase() != pattern.to_uppercase() {
            self.reset_cur(cur);
            return Err(err_expected_string(self.cur, pattern));
        }
 
        Ok(())
    }

    pub fn one_of_strings(&mut self, bs: &[&str]) -> ParseResult<()> {
        for b in bs {
            match self.string(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected string:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur)),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_strings(self.cur, bs))
    }

    pub fn one_of_strings_ic(&mut self, bs: &[&str]) -> ParseResult<()> {
        for b in bs {
            match self.string_ic(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected string:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur)),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_strings(self.cur, bs))
    }

    // get next n bytes as string
    pub fn get_string(&mut self, n: usize) -> ParseResult<String> {
        self.check_excess(n)?;
        let cur = self.cur;
        let v = self.get_bytes(n)?;
        match str::from_utf8(&v) {
            Ok(s)  => return Ok(s.to_string()),
            Err(std::str::Utf8Error{..}) => {
                self.reset_cur(cur);
                return Err(err_utf8_error(self.cur, v));
            },
        }
    }

    // bytes, sequence of (potentially) non-unicode bytes
    pub fn bytes(&mut self, pattern: &[u8]) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let mut cur = self.cur;
        let sav = cur;
        self.consume(n, false)?;
        for c in pattern {
            let b = self.get(cur);
            if *c != b {
               self.reset_cur(sav);
               return Err(err_expected_byte(self.cur, *c, b));
            }
            self.advance_this(&mut cur, 1);
        }
        Ok(())
    }

    // bytes, sequence of (potentially) non-unicode bytes
    pub fn get_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;
        let mut cur = self.cur;
        self.consume(n, false)?;

        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(self.get(cur)); 
            self.advance_this(&mut cur, 1);
        }
        Ok(v)
    }

    fn copy_from_bufs(&mut self, buf: &mut Vec<u8>) -> ParseResult<usize> {
        let l = buf.len();
        let mut s = 0;
        let mut p = self.cur.pos;
        let mut x = self.cur.buf;
        for i in 0 .. l {
            if p >= self.states[x].size {
                x += 1;
                x %= self.opts.buf_num;
                if !self.states[x].valid {
                    break;
                }
                p = 0;
            }
            buf[i] = self.bufs[x][p];
            p += 1;
            s += 1;
        }
        Ok(s)
    }

    // binary object size = buf.len()
    pub fn blob(&mut self, buf: &mut Vec<u8>) -> ParseResult<usize> {
        let l = buf.len();
        let mut s = self.copy_from_bufs(buf)?;
        while s < l {
            match self.reader.read(&mut buf[s..]) {
                Ok(0) => return Ok(0),
                Ok(x) => s += x,
                Err(ref e) if e.kind() == ErrorKind::Interrupted => continue,
                Err(e) => return Err(ParseError::IOError(e)),
            };
        }

        self.init()?;
        self.cur.pos = 0;
        self.cur.buf = 0;
        Ok(s)
    }

    // get everything in the buffers out
    pub fn drain(&mut self) -> ParseResult<Vec<u8>> {
        let mut v = Vec::new();
        let mut p = self.cur.pos;
        let mut x = self.cur.buf;
        loop {
            if p < self.states[x].size {
                v.extend_from_slice(&self.bufs[x][p..]);
            }
            self.states[x].valid = false;
            x += 1;
            x %= self.opts.buf_num;
            if !self.states[x].valid {
               break;
            }
            p = 0;
        }

        self.cur.pos = 0;
        self.cur.buf = 0;
        Ok(v)
    }

    pub fn peek_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1, true)?;
        let ch = self.get(cur);
        self.reset_cur(cur);
        Ok(ch)
    }

    pub fn peek_character(&mut self) -> ParseResult<char> {
        let cur = self.cur;
        match self.any_character() {
            Ok(ch) => {
                self.reset_cur(cur);
                return Ok(ch);
            },
            Err(e) => {
                self.reset_cur(cur);
                return Err(e);
            },    
        }
    }

    pub fn peek_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;

        let mut cur = self.consume(n, true)?;
        let sav = cur;
        let mut v = Vec::with_capacity(n);
        for _ in 0 .. n {
            v.push(self.get(cur));
            self.advance_this(&mut cur, 1);
        }
        self.reset_cur(sav);
        Ok(v)
    }

    pub fn peek_characters(&mut self, n: usize) -> ParseResult<Vec<char>> {

        self.check_excess(4*n)?; // sloppy 

        let sav = self.cur;

        let mut v = Vec::new();
        for _ in 0 .. n {
            match self.any_character() {
                Ok(ch) => v.push(ch),
                Err(e) => {
                    self.reset_cur(sav);
                    return Err(e);
                },
            }
        }
        self.reset_cur(sav);
        Ok(v)
    }

    // trait object or function?
    pub fn optional<T, F>(&mut self, parse: F) -> ParseResult<Option<T>> 
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
    {
        let cur = self.cur;
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
            let cur = self.cur;
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
            let cur = self.cur;
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
        let cur = self.cur;
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
        Err(err_all_failed(self.cur, v))
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
            let cur = self.cur;
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
            let cur = self.cur;
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
            let cur = self.cur;
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
            let cur = self.cur;
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
            let cur = self.cur;
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
