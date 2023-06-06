use crate::*;

/// Defines characteristics of the stream.
/// The fields should not be set directly.
/// Instead the setters should be used.
/// Otherwise your code may not be compatible
/// with future versions of the library.
#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Opts {
    /// Size of buffers in the stream.
    pub buf_size: usize,

    /// Number of buffers in the stream.
    pub buf_num: usize,

    /// Maximum number of bytes that are accepted
    /// in a stream.
    pub max_stream: u64,
}

/// The default values are:
///
/// * buf_size: 8192
///
/// * buf_num: 5
/// 
/// * max_stream: `u32::MAX`
///
/// Those settings are suitable for parsing large files.
/// Parsing from in-memory buffers or strings may use
/// smaller buffers. Parsing from a socket may require
/// setting `max_stream` to infinite.
impl Default for Opts {
    fn default() -> Opts {
        Opts {
            buf_size: 8192,
            buf_num: 5,
            max_stream: u32::MAX as u64,
        }
    }
}

// let opts = Opts::default()
//             .set_buf_num(5)
//             .set_infinite_stream();
impl Opts {
    /// Sets the buffer size. A robust way to use this function is:
    /// ``` 
    /// use pacosso::options::Opts;
    /// let opts = Opts::default()
    ///     .set_buf_size(256);
    /// ``` 
    /// This guarantees that `Opts` has meaningful settings
    /// even for fields that are added in the future.
    pub fn set_buf_size(self, s: usize) -> Opts {
        Opts {
            buf_size: s,
            buf_num: self.buf_num,
            max_stream: self.max_stream,
        }
    }

    /// Sets the number of buffers . A robust way to use this function is:
    /// ``` 
    /// use pacosso::options::Opts;
    /// let opts = Opts::default()
    ///     .set_buf_size(256)
    ///     .set_buf_num(3);
    /// ``` 
    /// This guarantees that `Opts` has meaningful settings
    /// even for fields that are added in the future.
    pub fn set_buf_num(self, s: usize) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: s,
            max_stream: self.max_stream,
        }
    }

    /// Sets the maximum stream size. A robust way to use this function is:
    /// ``` 
    /// use pacosso::options::Opts;
    /// let opts = Opts::default()
    ///     .set_buf_size(256)
    ///     .set_buf_num(3)
    ///     .set_max_stream(u16::MAX as u64);
    /// ``` 
    /// This guarantees that `Opts` has meaningful settings
    /// even for fields that are added in the future.
    pub fn set_max_stream(self, s: u64) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_stream: s,
        }
    }

    /// Sets the maximum stream size to infinite.
    /// A robust way to use this function is:
    /// ``` 
    /// use pacosso::options::Opts;
    /// let opts = Opts::default()
    ///     .set_buf_size(256)
    ///     .set_buf_num(3)
    ///     .set_infinite_stream();
    /// ``` 
    /// This guarantees that `Opts` has meaningful settings
    /// even for fields that are added in the future.
    pub fn set_infinite_stream(self) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_stream: 0,
        }
    }

    /// Validate the options provided to `Stream::new`.
    /// The function returns a `ParseError::Option`
    /// if the options are invalid. Currently only two rules are enforced:
    /// buffer size should be at least 8 bytes and buffer number should be at least 3.
    ///
    /// It is advisable to validate options before creating the stream.
    /// This avoids surprises at run-time (especially for future versions).
    ///
    /// Example:
    /// ``` 
    /// use pacosso::options::Opts;
    /// use pacosso::error::ParseError;
    /// let opts = Opts::default()
    ///     .set_buf_size(256)
    ///     .set_buf_num(3)
    ///     .set_infinite_stream();
    /// assert!(match opts.validate() {
    ///     Ok(()) => true,
    ///     Err(ParseError::Option(_)) => false,
    ///     _ => false,
    /// });
    /// let opts = opts.set_buf_num(1);
    /// assert!(match opts.validate() {
    ///     Ok(()) => false,
    ///     Err(ParseError::Option(ref m)) if m == "minimum number of bufs is 3" => true,
    ///     _ => false,
    /// });
    /// ``` 
    pub fn validate(&self) -> ParseResult<()> {
        if self.buf_size < 8 {
            return Err(ParseError::Option("minimum buf size is 8 bytes".to_string()));
        }
        if self.buf_num < 3 {
            return Err(ParseError::Option("minimum number of bufs is 3".to_string()));
        }
        Ok(())
    }
}

