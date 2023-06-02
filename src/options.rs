use crate::*;

#[derive(PartialEq, Eq, Hash, Debug)]
pub struct Opts {
    pub buf_size: usize,
    pub buf_num: usize,
    pub max_stream: u64,
    pub is_stream: bool,
}

impl Default for Opts {
    fn default() -> Opts {
        Opts {
            buf_size: 8192,
            buf_num: 5,
            max_stream: u32::MAX as u64,
            is_stream: false,
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
            max_stream: self.max_stream,
            is_stream: self.is_stream,
        }
    }
    pub fn set_buf_num(self, s: usize) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: s,
            max_stream: self.max_stream,
            is_stream: self.is_stream,
        }
    }
    pub fn set_max_stream(self, s: u64) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_stream: s,
            is_stream: self.is_stream,
        }
    }
    pub fn set_infinite_stream(self) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_stream: 0,
            is_stream: self.is_stream,
        }
    }
    pub fn set_stream(self) -> Opts {
        Opts {
            buf_size: self.buf_size,
            buf_num: self.buf_num,
            max_stream: self.max_stream,
            is_stream: true,
        }
    }
    pub fn validate(&self) -> ParseResult<()> {
        if self.buf_size < 8 {
            return Err(ParseError::Option("minimum buf size is 8 bytes".to_string()));
        }
        if self.buf_size < 3 {
            return Err(ParseError::Option("minimum number of bufs 2".to_string()));
        }
        Ok(())
    }
}

