//! _Pacosso_ is a framework for rapid parser development.
//! It does not aim at building high-performance parsers -
//! other frameworks are much more suitable for that -
//! but rather at easy development for rapid prototyping
//! and projects with moderate performance requirements.
//! 
//! Different from other streaming parser libraries,
//! _pacosso_ manages the incoming stream internally.
//! The feature is intended to make writing parsers
//! as easy as possible.
//! _Pacosso_ is able to handle any reader including
//! in-memory buffers and strings, files, sockets and
//! IO-chains combining such readers.
//!
//! Example:
//! ```
//! use std::io;
//! use pacosso::{Stream, ParseResult};
//! use pacosso::options::Opts;
//!
//! let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
//!     p.string("hello")?;
//!     p.whitespace()?;
//!     p.string("world")
//! };
//!
//! let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
//! let mut s = Stream::new(Opts::default(), &mut input);
//!
//! assert!(match s.apply(parse) {
//!     Ok(()) => true,
//!     Err(e) => {
//!        eprintln!("error: {:?}", e);
//!        false
//!     },
//! });
//! ```
//! 
//! [Jsosso] is a JSON parser that demonstrates the framework.
//! It contains demo programs, benchmarks and more documentation.
//! 
//! [Jsosso]: https://github.com/toschoo/jsosso

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

/// Parser methods return a `Result` of a generic type and a ParseError 
pub type ParseResult<T> = Result<T, ParseError>;

/// Cursor keeps track of the position
/// in the overall stream,
/// in terms of lines in the stream and
/// within the current line.
/// Note that, for `stream`, the start position is 0,
/// while, for `line` and `lpos`, the start position is 1.
///
/// `ParseError`s contain a cursor to point to the position
/// where the parser failed.
#[derive(Debug, Clone, Copy)]
pub struct Cursor {
    buf: usize,
    pos: usize,
    /// The current position in the the overall stream
    pub stream: u64,
    /// The current position in terms of lines in the stream.
    /// Note that lines are, currently, only counted as whitespace.
    /// This is somewhat sloppy and a better solution will be needed.
    pub line: u64,
    /// The current position within the current line
    pub lpos: u64,
}

impl fmt::Display for Cursor {
    fn fmt(&self, f: &mut fmt::Formatter) -> Result <(), fmt::Error> {
        write!(f, "absolute position {}, line {}, position {}",
               self.stream, self.line, self.lpos)
    }
}

type Buf = Vec<u8>;

#[derive(Debug, Clone, Copy)]
struct BufState {
    valid: bool,
    size: usize,
}

/// Stream manages the reader from which to parse.
/// Streams can be built from any reader including
/// in-memory buffers and strings, files, sockets
/// and `io::Chain`s.
///
/// Example:
/// ```
/// use std::io;
/// use pacosso::Stream;
/// use pacosso::options::Opts;
/// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
/// let s = Stream::new(Opts::default(), &mut input);
/// /* do something with s */
pub struct Stream<'a, R: Read> {
    // the data source
    reader: &'a mut R,
    // internal buffers
    bufs: Vec<Buf>, 
    // state of the buffers
    states: Vec<BufState>,
    // current position in the stream
    cur: Cursor,
    // options defined by the creator
    opts: Opts,
    // have we already initialised this stream?
    inited: bool,
    // table of whitespace bytes
    white_space: HashSet<u8>,
}

/// Convenience interface for parsing from a file.
///
/// Parameters:
///
/// * `f` - The path to the file as `OsString`
///
/// * `opts` - Options for `Stream` 
///
/// * `parse` - The parser function or closure
///
/// Example:
/// ```
/// use std::fs::File;
/// use std::ffi::OsString;
/// use pacosso::{Stream, parse_file, ParseResult};
/// use pacosso::options::Opts;
///
/// let parse = |p: &mut Stream<File>| -> ParseResult<()> {
///     p.succeed() // the simplest possible parser
/// };
///
/// assert!(match parse_file("./Cargo.toml".into(), Opts::default(), parse) {
///     Ok(()) => true,
///     Err(e) => {
///        eprintln!("error: {:?}", e);
///        false
///     },
/// });
/// ```
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

/// Convenience interface for parsing a string.
///
/// Parameters:
///
/// * `s` - The string to parse
///
/// * `opts` - Options for `Stream` 
///
/// * `parse` - The parser function or closure
///
/// Example:
/// ```
/// use std::io;
/// use pacosso::{Stream, parse_string, ParseResult};
/// use pacosso::options::Opts;
///
/// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
///     p.string("hello")?;
///     p.whitespace()?;
///     p.string("world")
/// };
///
/// assert!(match parse_string("hello world".to_string(), Opts::default(), parse) {
///     Ok(()) => true,
///     Err(e) => {
///        eprintln!("error: {:?}", e);
///        false
///     },
/// });
/// ```
pub fn parse_string<F, T>(s: String, opts: Opts, parse: F) -> ParseResult<T> 
         where F: Fn(&mut Stream<io::Cursor<Vec<u8>>>) -> ParseResult<T>
{
    let mut input = io::Cursor::new(s.as_bytes().to_vec());
    let mut p = Stream::new(opts, &mut input);
    parse(&mut p)
}

/// Convenience interface for parsing a byte buffer.
///
/// Parameters:
///
/// * `buf` - The buffer to parse
///
/// * `opts` - Options for `Stream` 
///
/// * `parse` - The parser function or closure
///
/// Example:
/// ```
/// use std::io;
/// use pacosso::{Stream, parse_buffer, ParseResult};
/// use pacosso::options::Opts;
///
/// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
///     p.string("hello")?;
///     p.whitespace()?;
///     p.string("world")
/// };
///
/// assert!(match parse_buffer(&"hello world".as_bytes().to_vec(), Opts::default(), parse) {
///     Ok(()) => true,
///     Err(e) => {
///        eprintln!("error: {:?}", e);
///        false
///     },
/// });
/// ```
pub fn parse_buffer<F, T>(buf: &[u8], opts: Opts, parse: F) -> ParseResult<T>
         where F: Fn(&mut Stream<io::Cursor<Vec<u8>>>) -> ParseResult<T>
{
    let mut input = io::Cursor::new(buf.to_vec());
    let mut p = Stream::new(opts, &mut input);
    parse(&mut p)
}

impl<'a, R: Read> Stream<'a, R> {

   /// Stream constructor.
   ///
   /// Parameters: 
   ///
   /// * `opts` - the stream options
   ///
   /// * `reader` - the reader from which to parse
   ///
   /// Example:
   /// ```
   /// use std::io;
   /// use pacosso::Stream;
   /// use pacosso::options::Opts;
   /// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
   /// let s = Stream::new(Opts::default(), &mut input);
   /// /* do something with s */
   /// ```
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
       self.opts.validate()?;

       for i in 1..self.opts.buf_num {
           self.states[i].valid = false;
           self.states[i].size  = self.opts.buf_size;
       }

       self.cur.stream = 0;
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

    /// Returns the size of internal buffers
    /// as defined by means of `Opts`.
    pub fn buf_size(self) -> usize {
        self.opts.buf_size
    }

    /// Returns the number of internal buffers
    /// as defined by means of `Opts`.
    pub fn buf_num(self) -> usize {
        self.opts.buf_num
    }

    /// Returns the maximal stream size
    /// as defined by means of `Opts`.
    /// If stream size is 0, the stream is infinite.
    pub fn max_stream(self) -> u64 {
        self.opts.max_stream
    }

    /// Defines the bytes that serve as whitespace.
    /// 
    /// By default whitespace bytes are:
    /// '` `', '`\n`', '`\r`' and '`\t`'.
    /// Note that currently only bytes can be defined as whitespace.
    /// Unicode characters outside the range of ASCII code cannot be used.
    ///
    /// Note further that if your set of whitespace bytes does not contain
    /// linebreaks, lines won't be counted.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new(" - _ - ".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// s.set_whitespace(&[b'-', b'_']);
    /// assert!(match s.whitespace() {
    ///     Ok(()) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.byte(b' ') {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.whitespace() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.byte(b' ') {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn set_whitespace(&mut self, w: &[u8]) {
        self.white_space = w.to_vec().into_iter().collect();
    }

    /// Returns the cursor pointing to the current position.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert_eq!(s.position().stream, 0);
    /// assert_eq!(s.position().line, 1);
    /// assert_eq!(s.position().lpos, 1);
    /// ```
    pub fn position(&self) -> Cursor {
        self.cur
    }

    /// Increments the line counter by one.
    /// Use this method if you don't have defined linebreak as whitespace.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// s.count_lines();
    /// assert_eq!(s.position().line, 2);
    /// assert_eq!(s.position().lpos, 1);
    /// ```
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
                    self.states[n].size = s;
                    if s < self.opts.buf_size {
                       if wanted > 0 && s < wanted {
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
            let d = self.opts.buf_size - self.states[buf].size;
            if n > d {
                return d;
            } else {
                return n;
            }
        }
    }

    // advance stream position and return old settings for cur
    fn consume(&mut self, n: usize) -> ParseResult<Cursor> {
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
                let wanted = self.bytes_to_read(j, r);

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

    /// The simplest possible parser. It always succeeds and does not consume anything.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input).succeed() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn succeed(&mut self) -> ParseResult<()> {
        Ok(())
    }

    /// Causes the parser to fail with error message `msg`.
    /// The parameter `dummy` defines the return type
    /// that would otherwise remain invisible.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::error::ParseError;
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("hello world".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(),&mut input)
    ///         .fail("cannot parse 'hello world'", ()) {
    ///     Err(ParseError::Failed(x, _)) if x == "cannot parse 'hello world'" => true,
    ///     Ok(()) => false,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn fail<T>(&mut self, msg: &str, _dummy: T) -> ParseResult<T> {
        Err(ParseError::Failed(msg.to_string(), self.cur))
    }

    /// Succeeds if the we reached the end of the input and fails otherwise.
    /// Does not consume anything.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input).eof() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn eof(&mut self) -> ParseResult<()> {
        match self.consume(1) {
            Ok(cur) => {
                self.reset_cur(cur);
                return Err(err_not_eof(self.cur));
            },
            Err(ParseError::Failed(s, _)) if s == "end of file" => return Ok(()),
            Err(e) => return Err(e),
        }
    }

    /// Consumes one byte and succeeds if this byte is `ch` and fails otherwise.
    /// Like all parser methods, it does not consume anything when failing.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("@".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// // fail
    /// assert!(match s.byte(b'a') {
    ///     Ok(()) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// // we did not consume anything
    /// assert!(match s.byte(b'@') {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// // we have consumed one byte and will fail now
    /// assert!(match s.byte(b'@') {
    ///     Ok(_) => false,
    ///     Err(e) if e.is_eof() => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn byte(&mut self, ch: u8) -> ParseResult<()> {
        let cur = self.consume(1)?;
        let b = self.get(cur);
        if b != ch {
            self.reset_cur(cur);
            return Err(err_expected_byte(self.cur, ch, b));
        }

        Ok(())
    }

    /// Consumes one byte and succeeds if this byte is in the set `bs` and fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("@".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.one_of_bytes(&[b'a', b'b', b'c']) {
    ///     Ok(()) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.one_of_bytes(&[b'a', b'b', b'@']) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    // we could use a set here. However, to create the set, we touch all elements once anyway.
    pub fn one_of_bytes(&mut self, bs: &[u8]) -> ParseResult<()> {
        let x = self.peek_byte()?;
        for b in bs {
            if x == *b {
                self.byte(x)?;
                return Ok(());
            }
        }
        Err(err_expected_one_of_bytes(self.cur, bs, x))
    }

    /// Consumes `pattern.len()` bytes and succeeds if these bytes equal `pattern` and fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("hello".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.bytes(&[b'h', b'a', b'l', b'l', b'o']) {
    ///     Ok(()) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.bytes(&[b'h', b'e', b'l', b'l', b'o']) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn bytes(&mut self, pattern: &[u8]) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let mut cur = self.cur;
        let sav = cur;
        self.consume(n)?;
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

    /// Consumes one byte and returns it. Fails if there are no more bytes to consume
    /// and succeeds otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("@".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.any_byte() {
    ///     Ok(b'@') => true,
    ///     Ok(_) => false,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.any_byte() {
    ///     Ok(_) => false,
    ///     Err(e) if e.is_eof() => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn any_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1)?;
        let ch = self.get(cur);
        Ok(ch)
    }

    /// Consumes up to `n` bytes and returns them in a vector;
    /// fails if there are less than `n` bytes left in the stream.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("hello".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.get_bytes(5) {
    ///     Ok(v) => v == [b'h', b'e', b'l', b'l', b'o'],
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn get_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;
        let mut cur = self.cur;
        self.consume(n)?;

        let mut v = Vec::with_capacity(n);
        for _ in 0..n {
            v.push(self.get(cur)); 
            self.advance_this(&mut cur, 1);
        }
        Ok(v)
    }

    /// Consumes up to 4 bytes and succeeds if the bytes read correspond
    /// to `ch` and fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("京".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.character('京') {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn character(&mut self, ch: char) -> ParseResult<()> {
        let mut b1 = [0; 4];
        let mut b2 = [0; 4];

        let n = ch.encode_utf8(&mut b1).len();

        let cur = self.consume(n)?;

        self.get_many(cur, n, &mut b2);

        // we convert the bytes to a char to ensure to apply unicode comparison rules.
        let s = match str::from_utf8(&b2[..n]) {
            Ok(s) => s,
            Err(_) => {
                self.reset_cur(cur);
                return Err(err_expected_char(self.cur, ch, &b2));
            },
        };

        let c2 = match s.chars().nth(0) {
            Some(c) => c,
            None => return Err(err_expected_char(self.cur, ch, &b2)),
        };

        if ch != c2 {
            self.reset_cur(cur);
            return Err(err_expected_char(self.cur, ch, &b2));
        }

        Ok(())
    }

    /// Consumes up to 4 bytes and succeeds if the bytes read correspond
    /// to a character in the set `cs` and fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("京".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.one_of_chars(&['@', 'ß', '京']) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn one_of_chars(&mut self, cs: &[char]) -> ParseResult<()> {
        let x = self.peek_character()?;
        for c in cs {
            if x == *c {
                self.character(x)?;
                return Ok(());
            }
        }
        Err(err_expected_one_of_chars(self.cur, cs, x))
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

    /// Consumes up to four bytes and returns them as char.
    /// Fails if there are not enough bytes to consume
    /// or if those byte do not form a valid unicode char;
    /// succeeds otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("京".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.any_character() {
    ///     Ok(ch) => ch == '京',
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn any_character(&mut self) -> ParseResult<char> {
        let mut bs = [0; 4];

        let cur = self.consume(1)?;
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
            let cur = match self.consume(1) {
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

    /// Consumes one byte and succeeds if this byte is the ASCII encoding of a digit,
    /// i.e. the byte is `>= 48` and `<= 57`; fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("1 2 3".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.digit() {
    ///     Ok(n) => n == b'1', // note that we are reading an ASCII byte, not a number
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn digit(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1)?;
        let ch = self.get(cur);
        if ch < 48 || ch > 57 {
            self.reset_cur(cur);
            return Err(err_not_a_digit(self.cur, ch));
        }
        Ok(ch)
    }

    /// Calls `digit()` until it fails. Succeeds if digit succeeds at least once
    /// and fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("123 4 5".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.digits() {
    ///     Ok(v) => v == [b'1', b'2', b'3'],
    ///     Err(_) => false,
    /// });
    /// assert!(match s.digits() {
    ///     Ok(_) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.byte(b' ') {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.digits() {
    ///     Ok(v) => v == [b'4'],
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn digits(&mut self) -> ParseResult<Vec<u8>> {
        let mut first = true;
        let mut v = Vec::new();
        loop {

            // we don't want to fail on eof if we read at least one digit 
            let cur = match self.consume(1) {
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

    /// Consumes bytes until it sees the first byte that is not in the whitespace set.
    /// Succeeds if at least one whitespace was read and fails otherwise.
    /// To just ignore whitespace (without failing), use `set_whitespace`.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("1 2 3".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.digit() {
    ///     Ok(n) => n == b'1',
    ///     Err(_) => false,
    /// });
    /// assert!(match s.whitespace() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.whitespace() {
    ///     Ok(()) => false,
    ///     Err(e) if e.is_expected_token() => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn whitespace(&mut self) -> ParseResult<()> {
        let mut first = true;
        loop {

            // we don't want to fail on eof if we read at least one whitespace char
            let cur = match self.consume(1) {
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

    /// Consumes bytes until it sees the first byte that is not in the whitespace set;
    /// `skip_whitespace` always succeeds.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::Stream;
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let mut input = io::Cursor::new("1 2 3".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.digit() {
    ///     Ok(n) => n == b'1',
    ///     Err(_) => false,
    /// });
    /// assert!(match s.skip_whitespace() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.skip_whitespace() {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// assert!(match s.digit() {
    ///     Ok(n) => n == b'2',
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn skip_whitespace(&mut self) -> ParseResult<()> {
        let _ = self.whitespace();
        Ok(())
    }

    /// Consumes up to `pattern.len()` bytes and succeeds if these byte correspond to `pattern`;
    /// fails otherwise.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input).string("BEGIN") {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn string(&mut self, pattern: &str) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let cur = self.cur;
        let s = self.get_string(n)?;
        if s != pattern {
            self.reset_cur(cur);
            return Err(err_expected_string(self.cur, pattern, &s));
        }
        Ok(())
    }

    /// Like `string()` but ignores case.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input).string_ic("Begin") {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn string_ic(&mut self, pattern: &str) -> ParseResult<()> {
        let n = pattern.len();
        self.check_excess(n)?;
        let cur = self.cur;
        let s = self.get_string(n)?;

        if s.to_uppercase() != pattern.to_uppercase() {
            self.reset_cur(cur);
            return Err(err_expected_string(self.cur, pattern, &s));
        }
 
        Ok(())
    }

    /// Succeeds if `string()` succeeds for one of the strings in `vs`; fails otherwise.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input)
    ///        .one_of_strings(&["BEGIN", "begin", "Begin"]) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    pub fn one_of_strings(&mut self, vs: &[&str]) -> ParseResult<()> {
        for b in vs {
            match self.string(*b) {
                Ok(()) => return Ok(()),
                Err(ParseError::Failed(x, _)) => match x.strip_prefix("expected string:") {
                    Some(_) => continue,
                    None => return Err(ParseError::Failed(x, self.cur)),
                }
                Err(e) => return Err(e),
            }
        }
        Err(err_expected_one_of_strings(self.cur, vs))
    }


    /// Like `one_of_strings()` but ignores case.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// assert!(match Stream::new(Opts::default(), &mut input)
    ///        .one_of_strings_ic(&["begin", "start"]) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
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

    /// Consumes up to `n` bytes and succeeds if these bytes form a valid unicode string;
    /// fails otherwise.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<String> {
    ///     p.string("BEGIN")?;
    ///     p.whitespace()?;
    ///     let s = match p.get_string(12) {
    ///         Ok(s) => s,
    ///         Err(e) => return p.fail("expected string", "".to_string()),
    ///     };
    ///     p.skip_whitespace()?;
    ///     p.byte(b'(')?;
    ///     p.skip_whitespace()?;
    ///     p.byte(b')')?;
    ///     p.skip_whitespace()?;
    ///     p.byte(b';')?;
    ///     p.whitespace()?;
    ///     p.string("END")?;
    ///     Ok(s)
    /// };
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(sym) if sym == "do_something" => true,
    ///     Ok(_) => false,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Consumes `buf.len()` bytes and places them into `buf`.
    /// Fails if there are not enough bytes to consume and succeeds otherwise.
    /// An important detail is that `blob()`, once the internal buffers are exhausted,
    /// bypasses the internal buffers. That is, the stream is read directly into `buf`.
    /// This is meant to speed up reading binary large objects (e.g. images, videos, etc.)
    /// but may render the stream unusable if `blob` fails unexpectedly.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let mut input = io::Cursor::new(vec![1; 128]);
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let mut v = vec![0; 128];
    /// let expected = vec![1; 128];
    /// assert!(match s.blob(&mut v) {
    ///     Ok(128) if v == expected => true,
    ///     Ok(_) => false,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn blob(&mut self, buf: &mut Vec<u8>) -> ParseResult<usize> {
        let l = buf.len();
        if !self.inited {
            self.init()?;
        }
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

    /// Returns the content of the internal buffers as a vector and always succeeds.
    /// Use `drain()` if you want to continue working on the stream without the stream.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use std::io::Read;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.string("BEGIN")?;
    ///     p.whitespace()?;
    ///     p.string("algol_type_program()")?;
    ///     p.skip_whitespace()?;
    ///     p.byte(b';')?;
    ///     p.skip_whitespace()?;
    ///     p.string("END")?;
    ///     p.skip_whitespace()
    /// };
    /// let mut input = io::Cursor::new(
    ///     r"BEGIN algol_type_program(); END
    ///     something completely different here".as_bytes().to_vec());
    /// let v = {
    ///    let mut s = Stream::new(Opts::default(), &mut input);
    ///    assert!(match parse(&mut s) {
    ///        Ok(()) => true,
    ///        Err(_) => false,
    ///    });
    ///    let v = s.drain(); // get buffer content out
    ///    match v {
    ///        Ok((v)) => v,
    ///        Err(e) => panic!("drain failed: {:?}", e),
    ///    }
    /// }; // drop s here
    /// let expected = "something completely different here".as_bytes().to_vec();
    /// let mut v2 = vec![0; expected.len()];  
    /// // read drained buffers and remaining input
    /// let _ = io::Cursor::new(v).chain(input).read(&mut v2);
    /// assert!(v2 == expected);
    /// ```
    pub fn drain(&mut self) -> ParseResult<Vec<u8>> {
        let mut v = Vec::new();
        if !self.inited {
            return Ok(v);
        }
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

    /// Returns the next byte to read without consuming it.
    /// Fails if there is nothing to consume.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     let b = p.peek_byte()?;
    ///     if b == b'[' {
    ///        p.byte(b'[')?; // always succeeds
    ///     }
    ///     Ok(())
    /// };
    /// let mut input = io::Cursor::new("[1, 2, 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn peek_byte(&mut self) -> ParseResult<u8> {
        let cur = self.consume(1)?;
        let ch = self.get(cur);
        self.reset_cur(cur);
        Ok(ch)
    }

    /// Returns the next `n` bytes to read without consuming them.
    /// Fails if there are less than `n` bytes left to consume.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b'[')?;
    ///     let vs = p.peek_bytes(7)?;
    ///     assert_eq!(vs, "1, 2, 3".as_bytes().to_vec());
    ///     Ok(())
    /// };
    /// let mut input = io::Cursor::new("[1, 2, 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn peek_bytes(&mut self, n: usize) -> ParseResult<Vec<u8>> {

        self.check_excess(n)?;

        let mut cur = self.consume(n)?;
        let sav = cur;
        let mut v = Vec::with_capacity(n);
        for _ in 0 .. n {
            v.push(self.get(cur));
            self.advance_this(&mut cur, 1);
        }
        self.reset_cur(sav);
        Ok(v)
    }

    /// Peeks up to four bytes without consuming them and
    /// returns them as `char`. Fails if the bytes read are not valid unicode
    /// or if there are not enough bytes. Succeeds otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b'[')?;
    ///     let ch = p.peek_character()?;
    ///     if ch == '🦀' {
    ///         p.character('🦀')?;
    ///     }
    ///     p.byte(b']')
    /// };
    /// let mut input = io::Cursor::new("[🦀]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Peeks `n` characters without consuming them.
    /// Fails if the bytes read are not valid unicode
    /// or if there are not enough bytes. Succeeds otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     let vs = p.peek_characters(3)?;
    ///     for v in &vs[..] {
    ///         let r = match v {
    ///             '[' => p.character('['),
    ///             '🦀' => p.character('🦀'),
    ///             ']' => p.character(']'),
    ///             _   => p.fail("unexpected character", ()),
    ///         };
    ///         match r {
    ///             Ok(_) => continue,
    ///             Err(e) => return p.fail(&format!("error: {:?}", e), ()),
    ///         }
    ///     }
    ///     Ok(())
    /// };
    /// let mut input = io::Cursor::new("[🦀[".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Applies `parse` and succeeds when `parse` succeeds; fails otherwise.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let mut v = Vec::new();
    ///     loop {
    ///         p.skip_whitespace()?;
    ///         let b = p.peek_byte()?;
    ///         if b == b']' {
    ///             break;
    ///         }
    ///         let n = p.digit()?;
    ///         v.push(n);
    ///     }
    ///     p.byte(b']')?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1 2 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = [b'1', b'2', b'3'];
    /// assert!(match s.apply(parse) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn apply<T, F>(&mut self, parse: F) -> ParseResult<T>
         where F: Fn(&mut Stream<R>) -> ParseResult<T>
    {
        parse(self)
    }

    /// Applies `parse` and succeeds even if `parse` fails.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let comma  = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b',')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b'[')?;
    ///     let mut i = b'1';
    ///     loop {
    ///         p.skip_whitespace()?;
    ///         let n = p.digit()?;
    ///         if n != i {
    ///             return p.fail("unexpected digit", ());
    ///         }
    ///         i += 1; 
    ///         match p.optional(comma) {
    ///             Ok(Some(())) => continue,
    ///             Ok(None) => break,
    ///             Err(_) => return p.fail("unexpected error", ()),
    ///         }
    ///     }
    ///     p.skip_whitespace()?;
    ///     p.byte(b']')?;
    ///     Ok(())
    /// };
    /// let mut input = io::Cursor::new("[1, 2, 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(()) => true,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Applies the `parsers` until
    /// one succeeds and returns the result of that one.
    /// It should be noted that `choice()` is inefficient in most cases,
    /// since it applies `n-1` parsers before it succeeds.
    ///
    /// Example
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let first_try = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<String> {
    ///     p.string("begin")?;
    ///     Ok("begin".to_string())
    /// };
    /// let second_try = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<String> {
    ///     p.string("Begin")?;
    ///     Ok("Begin".to_string())
    /// };
    /// let third_try = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<String> {
    ///     p.string("BEGIN")?;
    ///     Ok("BEGIN".to_string())
    /// };
    /// let parse = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     let choices = [first_try, second_try, third_try];
    ///     let s = p.choice(&choices[..])?;
    ///     Ok(())
    /// };
    /// let mut input = io::Cursor::new("BEGIN do_something(); END".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse(&mut s) {
    ///     Ok(v) => true,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Applies the three parsers in the order `before`, `parse` and `after`
    /// and returns the result of `parse`. All three parsers must succeed,
    /// otherwise `between` fails.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     let d = p.digit()?;
    ///     p.skip_whitespace()?;
    ///     Ok(d)
    /// };
    /// let opener = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b'[')
    /// };
    /// let closer = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b']')
    /// };
    /// let mut input = io::Cursor::new("[1]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match s.between(opener, digit, closer) {
    ///     Ok(v) if v == b'1' => true,
    ///     Ok(_) => false,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Applies `parse` until `parse` fails.
    /// Returns the results of all applications in a vector.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit  = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let v = p.many(digit)?;
    ///     p.skip_whitespace()?;
    ///     p.byte(b']')?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1 2 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("[]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v.len() == 0,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Like `many()` but fails if `parse` never succeeds.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit  = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let v = p.many_one(digit)?;
    ///     p.skip_whitespace()?;
    ///     p.byte(b']')?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1 2 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("[]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(_) => false,
    ///     Err(_) => true,
    /// });
    /// ```
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

    /// Applies `parse` until `stopper` succeeds and returns the results
    /// of all applications of `parse` in a vector. Fails if `parse` fails.
    /// It should be noted that `stopper` shall fail quickly. Otherwise,
    /// the resulting parser is not very efficient.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let stopper = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b']')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let v = p.until(digit, stopper)?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1 2 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// ```
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

    /// Applies `parse` until `sep` fails and returns the results of the applications
    /// of `parse` in a vector. Fails when `parse` fails excpet on the first term,
    /// i.e. parse never succeeding is allowed.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let sep = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b',')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let v = p.sep_by(digit, sep)?;
    ///     println!("{:?}", v);
    ///     p.byte(b']')?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1, 2, 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("[]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) if v.len() == 0 => true,
    ///     Ok(_)  => false,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn sep_by<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
    {
        let mut first = true;
        let mut v = Vec::new();
        let cur = self.cur;
        loop {
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
            let cur2 = self.cur;
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur2) {
                        self.reset_cur(cur2);
                    } else {
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    /// Like `sep_by` but fails if `parse` never succeeds.
    ///
    /// Example:
    ///
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let sep = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b',')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     p.byte(b'[')?;
    ///     let v = p.sep_by_one(digit, sep)?;
    ///     println!("{:?}", v);
    ///     p.byte(b']')?;
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("[1, 2, 3]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("[]".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(_)  => false,
    ///     Err(_) => true,
    /// });
    /// ```
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
            let cur2 = self.cur;
            match sep(self) {
                Ok(()) => continue,
                Err(e) => {
                    if self.resettable(cur2) {
                        self.reset_cur(cur2);
                    } else {
                        return Err(err_fatal(e));
                    }
                    break;
                },
            }
        }
        Ok(v)
    }

    /// Applies `parse` and `sep` until `parse` fails and returns the results of the successful applications
    /// of `parse` in a vector. Fails when `sep` fails.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let sep = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b',')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     let v = p.end_by(digit, sep)?;
    ///     println!("{:?}", v);
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("1, 2, 3,".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) if v.len() == 0 => true,
    ///     Ok(_) => false,
    ///     Err(_) => false,
    /// });
    /// ```
    pub fn end_by<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
    {
        let mut v = Vec::new();
        let cur = self.cur;
        loop {
            let cur2 = self.cur;
            match parse(self) {
                Ok(t) => v.push(t),
                Err(e) => {
                    if self.resettable(cur2) {
                        self.reset_cur(cur2);
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

    /// Like `end_by` but fails if `parse` never succeeds.
    ///
    /// Example:
    /// ```
    /// use std::io;
    /// use pacosso::{Stream, ParseResult};
    /// use pacosso::options::Opts;
    /// let digit = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<u8> {
    ///     p.skip_whitespace()?;
    ///     p.digit()
    /// };
    /// let sep = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<()> {
    ///     p.byte(b',')
    /// };
    /// let parse1 = |p: &mut Stream<io::Cursor<Vec<u8>>>| -> ParseResult<Vec<u8>> {
    ///     let v = p.end_by_one(digit, sep)?;
    ///     println!("{:?}", v);
    ///     Ok(v)
    /// };
    /// let mut input = io::Cursor::new("1, 2, 3,".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// let expected = vec![b'1', b'2', b'3'];
    /// assert!(match parse1(&mut s) {
    ///     Ok(v) => v == expected,
    ///     Err(_) => false,
    /// });
    /// let mut input = io::Cursor::new("".as_bytes().to_vec());
    /// let mut s = Stream::new(Opts::default(), &mut input);
    /// assert!(match parse1(&mut s) {
    ///     Ok(_) => false,
    ///     Err(_) => true,
    /// });
    /// ```
    pub fn end_by_one<T, F1, F2>(&mut self, parse: F1, sep: F2) -> ParseResult<Vec<T>>
         where F1: Fn(&mut Stream<R>) -> ParseResult<T>,
               F2: Fn(&mut Stream<R>) -> ParseResult<()>
    {
        let mut first = true;
        let mut v = Vec::new();
        let cur = self.cur;
        loop {
            let cur2 = self.cur;
            match parse(self) {
                Ok(t) => {
                     first = false;
                     v.push(t);
                },
                Err(e) => {
                    if self.resettable(cur2) {
                        self.reset_cur(cur2);
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
