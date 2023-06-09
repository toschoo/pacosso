use crate::*;
use std::io;
use std::iter::{once, repeat};
// use std::assert_matches::assert_matches; // waiting for this one

type Input = io::Cursor<Vec<u8>>;
type ByteStream<'a> = Stream<'a, Input>;
type ChainedStream<'a> = Stream<'a, io::Chain<Input, Input>>;

fn to_stream(input: &mut Input) -> ByteStream {
   Stream::new(Opts::default()
               .set_buf_size(8)
               .set_buf_num(3),
               input)
}

fn tiny_stream() -> Input {
   Input::new(repeat('@' as u8).take(32).collect())
}
 
fn tiny_digit_stream() -> Input {
   Input::new(vec![48, 49, 50, 51, 52, 53, 54, 55, 56, 57])
}
 
fn tiny_alphanum_stream() -> Input {
   Input::new(vec![48, 49, 50, 51, 52, 53, 65, 54, 55, 56, 57])
}

fn tiny_u16_stream() -> Input {
   Input::new(repeat('ß').take(32).collect::<String>()
                  .as_bytes().to_vec()
   )
}

fn tiny_u32_stream() -> Input {
   Input::new(repeat('京').take(32).collect::<String>()
              .as_bytes().to_vec()
   )
}

fn tiny_mixed_char_stream() -> Input {
   Input::new(once("@ß京🦀").cycle().take(2).collect::<String>()
              .as_bytes().to_vec()
   )
}

fn tiny_mixed_invalid_stream() -> Input {
   Input::new(once([64, 195, 159, 228, 186, 172, 240, 159, 166, 128, 255].to_vec())
              .flatten().cycle().take(22).collect()
   )
}

fn tiny_ws_stream() -> Input {
   Input::new(repeat(' ' as u8).take(8).chain(
              repeat('@' as u8).take(8)).chain(
              repeat(' ' as u8).take(4)).chain(
              once('.'   as u8)).collect()
   )
}

fn tiny_sep_stream() -> Input {
   Input::new(once('@' as u8).chain(
              once(',' as u8)).cycle().take(32).chain(
              once('@' as u8)).collect()
   )
}

fn curly_brackets_stream() -> Input {
    Input::new(vec!['{' as u8,
                     '1' as u8,
                     '2' as u8,
                     '3' as u8,
                     '}' as u8]
   )
}

fn json_stream() -> Input {
    let s = r#"{
                "id" = 1,
                "a" = "hello"
                } 
                "#.to_string();
    let l = s.len() * 3;
    Input::new(s
               .as_bytes().iter()
               .map(|c: &u8| -> u8 {
                        *c
                })
               .cycle()
               .take(l)
               .collect::<Vec<u8>>()
   )
}

fn tiny_end_stream() -> Input {
   Input::new(once('@' as u8).chain(
              once(',' as u8)).cycle().take(32)
              .collect()
   )
}

fn pascal_stream() -> Input {
   Input::new("IF something THEN BEGIN do_something(); END IF"
               .to_string()
               .as_bytes()
               .to_vec()
   )
}

fn pseudo_binary_stream() -> Input {
    Input::new(r#"<image size="99">"#
               .as_bytes().to_vec().into_iter()
               .chain(repeat(b'@').take(99)).chain(
               r#"</image>"#.as_bytes().to_vec().into_iter())
               .collect()
    )
}

fn pseudo_binary_stream2() -> Input {
    Input::new("body size:99\n"
               .as_bytes().to_vec().into_iter()
               .chain(repeat(b'@').take(99))
               .collect()
    )
}


#[test]
fn test_succeed() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.succeed() {
        Ok(_) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_fail() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.fail("we are failing deliberately", ()) {
        Err(ParseError::Failed(s, _)) if s == "we are failing deliberately" => true,
        Err(e) => panic!("unexpected error: {:?}", e),
        Ok(_) => panic!("not failing on fail"),
    });
}

#[test]
fn test_eof() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
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
fn test_expected_byte() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.byte('@' as u8) {
        Ok(()) => true,
        Err(e) => panic!("error: {:?}", e),
    })
}

#[test]
fn test_unexpected_byte() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.byte('?' as u8) {
        Ok(()) => panic!("unexpected byte accepted"),
        Err(e) => match e {
                       ParseError::Failed(s, _) =>
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
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    for i in 0..32 {
        assert!(match s.byte('@' as u8) {
            Ok(()) => true,
            Err(e) => panic!("error in {}: {:?}", i, e),
        })
    }
}

#[test]
fn test_33_expected_bytes() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    for i in 0..33 {
        assert!(match s.byte('@' as u8) {
            Ok(()) if i == 32 => panic!("1 byte too many!"),
            Ok(()) => continue,
            Err(e) if i == 32  => match e {
                           ParseError::Failed(s, _) if s == "end of file" => true,
                           _ => panic!("unexpected error: {:?}", e),
                      },
            Err(e) => panic!("unexpected error: {:?} at {}", e, i),
        })
    }
}

#[test]
fn test_expected_char() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.character('@') {
        Ok(()) => true,
        Err(e) => panic!("error: {:?}", e),
    })
}

#[test]
fn test_expected_u16_char() {
    let mut input = tiny_u16_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.character('ß') {
        Ok(()) => true,
        Err(e) => panic!("error: {:?}", e),
    })
}

#[test]
fn test_unexpected_u16_char() {
    let mut input = tiny_u16_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.character('ö') {
        Ok(()) => panic!("unexpected char accepted"),
        Err(e) => match e {
                       ParseError::Failed(s, _) =>
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
    let mut input = tiny_u16_stream();
    let mut s = to_stream(&mut input);
    for _ in 0..32 {
        assert!(match s.character('ß') {
            Ok(()) => true,
            Err(e) => panic!("error: {:?}", e),
        })
    }
}

#[test]
fn test_33_expected_chars() {
    let mut input = tiny_u16_stream();
    let mut s = to_stream(&mut input);
    for i in 0..33 {
        assert!(match s.character('ß') {
            Ok(()) if i == 32 => panic!("1 char too many!"),
            Ok(()) => continue,
            Err(e) if i == 32  => match e {
                           ParseError::Failed(s, _) if s == "end of file" => true,
                           _ => panic!("unexpected error: {:?}", e),
                      },
            Err(e) => panic!("unexpected error: {:?} at {}", e, i),
        })
    }
}

#[test]
fn test_expected_u32_char() {
    let mut input = tiny_u32_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.character('京') {
        Ok(()) => true,
        Err(e) => panic!("error: {:?}", e),
    })
}

#[test]
fn test_unexpected_u32_char() {
    let mut input = tiny_u32_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.character('中') {
        Ok(()) => panic!("unexpected char accepted"),
        Err(e) => match e {
                       ParseError::Failed(s, _) =>
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
    let mut input = tiny_u32_stream();
    let mut s = to_stream(&mut input);
    for i in 0..32 {
        assert!(match s.character('京') {
            Ok(()) => true,
            Err(e) => panic!("error: {:?} at {}", e, i),
        })
    }
}

#[test]
fn test_33_expected_u32_char() {
    let mut input = tiny_u32_stream();
    let mut s = to_stream(&mut input);
    for i in 0..33 {
        assert!(match s.character('京') {
            Ok(()) if i == 32 => panic!("1 byte too many!"),
            Ok(()) => continue,
            Err(e) if i == 32  => match e {
                           ParseError::Failed(s, _) if s == "end of file" => true,
                           _ => panic!("unexpected error: {:?}", e),
                      },
            Err(e) => panic!("unexpected error: {:?} at {}", e, i),
        })
    }
}

#[test]
fn test_whitespace() {
    let mut input = tiny_ws_stream();
    let mut s = to_stream(&mut input);
    
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
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    s.set_whitespace(&[b' ', b'\n', b'@']);
    assert!(match s.whitespace() {
        Ok(()) => true,
        Err(e) => panic!("error: {:?}", e),
    });

    assert!(match s.whitespace() {
        Err(ParseError::Failed(s, _)) if s == "end of file" => true,
        Ok(()) => panic!("Ok but 'end of file' expected"),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_any_byte() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.any_byte() {
        Ok(64) => true, // 64 = @
        Ok(ch) => panic!("unexpected byte: {}", ch),
        Err(e) => panic!("error: {:?}", e),
    });
}

#[test]
fn test_many_bytes() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    for _ in 0 .. 32 {
        assert!(match s.any_byte() {
            Ok(64) => true, // 64 = @
            Ok(ch) => panic!("unexpected byte: {}", ch),
            Err(e) => panic!("error: {:?}", e),
        });
    }

    assert!(match s.any_byte() {
        Err(ParseError::Failed(s, _)) if s == "end of file" => true,
        Ok(ch) => panic!("OK but eof expected: {}", ch),
        Err(e) => panic!("error: {:?}", e),
    });
}

#[test]
fn test_peek_byte() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
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
        Err(ParseError::Failed(s, _)) if s == "end of file" => true,
        Ok(ch) => panic!("OK but eof expected: {}", ch),
        Err(e) => panic!("error: {:?}", e),
    });

    assert!(match s.any_byte() {
        Err(ParseError::Failed(s, _)) if s == "end of file" => true,
        Ok(ch) => panic!("OK but eof expected: {}", ch),
        Err(e) => panic!("error: {:?}", e),
    });
}

#[test]
fn test_peek_bytes() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
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
        Err(ParseError::Failed(s, _)) if s == "end of file" => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_peek_too_many_bytes() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.peek_bytes(15) {
        Ok(v) if v.len() == 15 => true,
        Ok(_) => panic!("unexpected result"),
        Err(e) => panic!("error: {:?}", e),
    });
    assert!(match s.peek_bytes(16) {
        Ok(_) => panic!("unexpected result"),
        Err(ParseError::Failed(s, _)) => 
            match s.strip_prefix("parser needs more buffer space") {
               Some(_) => true,
               _ => panic!("unexpected error: {}", s),
            },
        Err(e) => panic!("error: {:?}", e),
    });
}

#[test]
fn test_digit() {
    let mut input = tiny_digit_stream();
    let mut s = to_stream(&mut input);
    for i in 0 .. 10 {
        assert!(match s.digit() {
            Ok(n) => n == i + 48, 
            Err(e) => panic!("unexpected error: {}", e),
        });
    }
    let mut input2 = tiny_ws_stream();
    let mut w = to_stream(&mut input2);
    assert!(match w.digit() {
            Ok(n) => panic!("OK without digit in stream: {}", n),
            Err(ParseError::Failed(x, _)) =>
                match x.strip_prefix("expected ascii digit") {
                    Some(_) => true,
                    _       => panic!("unexpected error: {}", x),
                },
            Err(e) => panic!("unexpected error: {}", e),
    });
}

#[test]
fn test_digits() {
    let mut input = tiny_alphanum_stream();
    let mut s = to_stream(&mut input);
    assert!(match s.digits() {
        Ok(v) => match v[..] {
             [48, 49, 50, 51, 52, 53] => true,
             _ => panic!("unexpected result"),
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_curly_brackets() {
    let mut input = curly_brackets_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<(u8,u8,u8)> {
        let a = p.digit()?;
        let b = p.digit()?;
        let c = p.digit()?;
        Ok((a,b,c))
    };
    let before = |p: &mut ByteStream| -> ParseResult<()> { p.byte('{' as u8) };
    let after  = |p: &mut ByteStream| -> ParseResult<()> { p.byte('}' as u8) };

    assert!(match s.between(&before, &parse, &after) {
        Ok((b'1', b'2', b'3')) => true,
        Ok(n) => panic!("unexpected value: {:?}", n),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_many() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    assert!(match s.many(&parse) {
        Ok(v) if v.len() == 32 => true,
        Ok(n) => panic!("unexpected value: {:?}", n),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
} 

#[test]
fn test_many_0() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('o' as u8) };
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
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    assert!(match s.many_one(&parse) {
        Ok(v) if v.len() == 32 => true,
        Ok(n) => panic!("unexpected value: {:?}", n),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
} 

#[test]
fn test_many_one_0() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('o' as u8) };
    assert!(match s.many_one(&parse) {
        Ok(n) => panic!("unexpected value: {:?}", n),
        Err(ParseError::Failed(e, _)) =>
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
    let mut input = curly_brackets_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<u8> {
        p.any_byte()
    };
    let stop = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte('}' as u8)
    };
    assert!(match s.until(&parse, &stop) {
        Ok(v) if v.len() == 4 => true,
        Ok(n) => panic!("unexpected value: {:?}", n),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_choice() {
    let mut input = curly_brackets_stream();
    let mut s = to_stream(&mut input);
    let good = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte(b'{')?;
        p.succeed()
    };
    let bad1 = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte(b'(')?;
        p.fail("read '('", ())
    };
    let bad2 = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte(b'[')?;
        p.fail("read '['", ())
    };
    let v = [bad1, bad2, good];
    assert!(match s.choice(&v) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_fail_choice() {
    let mut input = curly_brackets_stream();
    let mut s = to_stream(&mut input);
    let bad1 = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte(b'(')?;
        p.fail("read '('", ())
    };
    let bad2 = |p: &mut ByteStream| -> ParseResult<()> {
        p.byte(b'[')?;
        p.fail("read '['", ())
    };
    let bad3 = |p: &mut ByteStream| -> ParseResult<()> {
        p.string("BEGIN")?;
        p.fail("read 'BEGIN'", ())
    };
    let v = [bad1, bad2, bad3];
    assert!(match s.choice(&v) {
        Ok(()) => panic!("unexpected success"),
        Err(e) if e.is_choice_failed() => match e {
            ParseError::Effect(_, _, ref v) if v.len() == 3 => true,
            _ => false,
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_optional() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse_ok = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let parse_fail = |p: &mut ByteStream| -> ParseResult<()> { p.byte('o' as u8) };

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
    let mut input = tiny_sep_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by(&parse, &sep) {
        Ok(v) if v.len() == 17 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_sep_by_1() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by(&parse, &sep) {
        Ok(v) if v.len() == 1 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_sep_by_0() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('0' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by(&parse, &sep) {
        Ok(v) if v.len() == 0 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_sep_by_one() {
    let mut input = tiny_sep_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by_one(&parse, &sep) {
        Ok(v) if v.len() == 17 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_sep_by_one_1() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by(&parse, &sep) {
        Ok(v) if v.len() == 1 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_sep_by_one_0() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('0' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.sep_by_one(&parse, &sep) {
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(ParseError::Failed(s, _)) => 
            match s.strip_prefix("expected byte:") {
                Some(_) => true,
                _       => panic!("unexpected error: {}", s),
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_end_by() {
    let mut input = tiny_end_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.end_by(&parse, &sep) {
        Ok(v) if v.len() == 16 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_no_end() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('@' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.end_by(&parse, &sep) {
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(ParseError::Failed(s, _)) => 
            match s.strip_prefix("expected byte:") {
                Some(_) => true,
                _       => panic!("unexpected error: {}", s),
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_end_by_0() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('o' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.end_by(&parse, &sep) {
        Ok(v) if v.len() == 0 => true,
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_end_by_one() {
    let mut input = tiny_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { p.byte('o' as u8) };
    let sep   = |p: &mut ByteStream| -> ParseResult<()> { p.byte(',' as u8) };

    assert!(match s.end_by_one(&parse, &sep) {
        Ok(v) => panic!("unexpected value: {:?}", v),
        Err(ParseError::Failed(s, _)) => 
            match s.strip_prefix("expected byte:") {
                Some(_) => true,
                _       => panic!("unexpected error: {}", s),
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_string() {
    let mut input = pascal_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { 
        p.string("IF")?;
        p.whitespace()?;
        p.string("something")?;
        p.whitespace()?;
        p.string("THEN")?;
        p.whitespace()?;
        p.string("BEGIN")?;
        p.whitespace()?;
        p.string("do_something()")?;
        let _ = p.whitespace();
        p.byte(';' as u8)?;
        p.whitespace()?;
        p.string("END")?;
        p.whitespace()?;
        p.string("IF")?;
        Ok(())
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_string_fail() {
    let mut input = pascal_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> { 
        p.string("IF")?;
        p.whitespace()?;
        p.string("something")?;
        p.whitespace()?;
        p.string("then")?;
        p.whitespace()?;
        p.string("BEGIN")?;
        p.whitespace()?;
        p.string("do_something()")?;
        let _ = p.whitespace();
        p.byte(';' as u8)?;
        p.whitespace()?;
        p.string("END")?;
        p.whitespace()?;
        p.string("IF")?;
        Ok(())
    };
    assert!(match parse(&mut s) {
        Ok(()) => panic!("lowercase accepted as uppercase"),
        Err(ParseError::Failed(e, _)) => match e.strip_prefix("expected string:") {
            Some(_) => true,
            _       => panic!("unexpected error: {:?}", e),
        },
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_string_ic() {
    let mut input = pascal_stream();
    let mut s = to_stream(&mut input);
    let skip_whitespace = |p: &mut ByteStream| -> ParseResult<()> { p.whitespace() };
    let parse = |p: &mut ByteStream| -> ParseResult<()> { 
        p.string_ic("IF")?;
        p.whitespace()?;
        p.string("something")?;
        p.whitespace()?;
        p.string_ic("then")?;
        p.whitespace()?;
        p.string_ic("Begin")?;
        p.whitespace()?;
        p.string_ic("do_Something()")?;
        p.optional(&skip_whitespace)?;
        p.string_ic(";")?;
        p.whitespace()?;
        p.string_ic("END")?;
        p.whitespace()?;
        p.string_ic("IF")?;
        Ok(())
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_blob() {
    let mut input = pseudo_binary_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<usize> {
        let mut v = Vec::with_capacity(99);
        v.resize(99, b'0');

        p.byte(b'<')?;
        p.string("image")?;

        p.whitespace()?;

        p.string("size")?;
        p.byte(b'=')?;
        p.byte(b'"')?;
        p.string("99")?;
        p.byte(b'"')?;

        p.byte(b'>')?;

        let sz = p.blob(&mut v)?;

        p.byte(b'<')?;
        p.byte(b'/')?;
        p.string("image")?;
        p.byte(b'>')?;
        Ok(sz)
    };
    assert!(match parse(&mut s) {
        Ok(sz) if sz == 99 => true,
        Ok(sz) => panic!("unexpected number of bytes: {}", sz),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_blob_eof() {
    let mut input = pseudo_binary_stream2();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<usize> {
        let mut v = Vec::with_capacity(99);
        v.resize(99, b'0');

        p.string("body")?;

        p.whitespace()?;

        p.string("size")?;
        p.byte(b':')?;
        p.string("99")?;

        p.byte(b'\n')?;

        let sz = p.blob(&mut v)?;

        p.eof()?;

        Ok(sz)
    };
    assert!(match parse(&mut s) {
        Ok(sz) if sz == 99 => true,
        Ok(sz) => panic!("unexpected number of bytes: {}", sz),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_fail_blob_eof() {
    let mut input = curly_brackets_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<usize> {
        let mut v = Vec::with_capacity(99);
        v.resize(99, b'0');

        p.byte(b'{')?;
        let _ = p.digits()?;
        p.byte(b'}')?;
        p.blob(&mut v)
    };
    assert!(match parse(&mut s) {
        Ok(0) => true,
        Ok(sz) => panic!("unexpected success: {}", sz),
        Err(e) => panic!("unexpected error: {:?}", e),
    });
    assert!(match s.eof() {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_drain() {
    // IF something THEN BEGIN do_something(); END IF
    let mut input = pascal_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {
        p.string("IF")?;
        p.whitespace()?;
        p.string("something")?;

        let v = p.drain()?;
        match str::from_utf8(&v) {
            Ok(" THE") => return Ok(()),
            Ok(x) => return p.fail(&format!("unexpected value: {}", x), ()),
            Err(e) => return p.fail(&format!("unexpected error: {:?}", e), ()),
        }
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_drain_and_continue() {
    // IF something THEN BEGIN do_something(); END IF
    let mut input = pascal_stream();
    let mut s = to_stream(&mut input);
    let parse1 = |p: &mut ByteStream| -> ParseResult<Vec<u8>> {
        p.string("IF")?;
        p.whitespace()?;

        let v = p.drain()?;
        match str::from_utf8(&v) {
            Ok("somet") => return Ok(v),
            Ok(x) => return p.fail(&format!("unexpected value: '{}'", x), v),
            Err(e) => return p.fail(&format!("unexpected error: {:?}", e), v),
        }
    };
    let parse2 = |p: &mut ChainedStream| -> ParseResult<()> {
        p.string("something")?;
        p.whitespace()?;
        p.string("THEN")?;
        p.whitespace()?;
        p.string("BEGIN")?;
        p.whitespace()?;
        p.string("do_something")?;
        p.skip_whitespace()?;
        p.character('(')?;
        p.character(')')?;
        p.character(';')?;
        p.skip_whitespace()?;
        p.string("END")?;
        p.skip_whitespace()?;
        p.string("IF")?;
        p.eof()
    };
    let v = match parse1(&mut s) {
        Ok(v) => v,
        Err(e) => panic!("unexpected error: {:?}", e),
    };

    println!("continuing with next stream");
    let mut chain = io::Cursor::new(v).chain(input);
    let mut s = Stream::new(Opts::default()
                    .set_buf_size(8)
                    .set_buf_num(3),
                    &mut chain,
    );
    assert!(match parse2(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    })
}

#[test]
fn test_parse_and_continue() {
    let mut input = json_stream();
    let mut s = to_stream(&mut input);

    let parse1 = |p: &mut  ByteStream| -> ParseResult<()> {
        p.whitespace()
    };

    let parse2 = |p: &mut ByteStream| -> ParseResult<(String, String)> {
        p.byte(b'{')?;
        p.skip_whitespace()?;

        p.byte(b'"')?;
        p.string("id")?;
        p.byte(b'"')?;
        p.skip_whitespace()?;
        p.byte(b'=')?;
        p.skip_whitespace()?;
        let x = p.get_string(1)?;
        p.skip_whitespace()?;

        p.byte(b',')?;

        p.skip_whitespace()?;
        p.byte(b'"')?;
        p.string("a")?;
        p.byte(b'"')?;

        p.skip_whitespace()?;
        p.byte(b'=')?;
        p.skip_whitespace()?;

        p.byte(b'"')?;
        let a = p.get_string(5)?;
        p.byte(b'"')?;

        p.skip_whitespace()?;
        p.byte(b'}')?;

        Ok((x, a))
    };

    for i in 0 .. 3 {
        let r = match parse2(&mut s) {
            Ok(t) => t,
            Err(e) => panic!("unexpected error: {:?} in {}", e, i),
        };

        assert!(match r {
            (a, b) if a == "1" && b == "hello" => true,
            (a, b) => panic!("unexpected result: {} / {}", a, b),
        });

        assert!(match parse1(&mut s) {
            Ok(()) => true,
            Err(e) => panic!("unexpected error: {:?}", e),
        });
    }
}

#[test]
fn test_any_char() {
    let mut input = tiny_mixed_char_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {
        for _ in 0 .. 2 {
            let c = p.any_character()?;
            if c != '@' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != 'ß' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != '京' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != '🦀' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
        }
        p.eof()
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_valid_and_invalid_chars() {
    let mut input = tiny_mixed_invalid_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {
        for _ in 0 .. 2 {
            let c = p.any_character()?;
            if c != '@' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != 'ß' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != '京' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let c = p.any_character()?;
            if c != '🦀' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            let _ = match p.any_character() {
                Ok(c) => return p.fail(&format!("unexpected character: '{}'", c), ()),
                Err(e) if e.is_utf8_error() => true,
                Err(e) => return p.fail(&format!("unexpected error: '{:?}'", e), ()),
            };
            p.byte(255)?;
        }
        p.eof()
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_peek_valid_and_invalid_chars() {
    let mut input = tiny_mixed_invalid_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {
        for _ in 0 .. 2 {
            let c = p.peek_character()?;
            if c != '@' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            p.character('@')?;

            let c = p.peek_character()?;
            if c != 'ß' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            p.character('ß')?;

            let c = p.peek_character()?;
            if c != '京' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            p.character('京')?;
            let c = p.peek_character()?;
            if c != '🦀' {
                return p.fail(&format!("unexpected character: '{}'", c), ());
            }
            p.character('🦀')?;

            let _ = match p.peek_character() {
                Ok(c) => return p.fail(&format!("unexpected character: '{}'", c), ()),
                Err(e) if e.is_utf8_error() => true,
                Err(e) => return p.fail(&format!("unexpected error: '{:?}'", e), ()),
            };
            p.byte(255)?;
        }
        p.eof()
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_peek_chars() {
    let mut input = tiny_mixed_char_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {
        for _ in 0 .. 2 {
            p.character('@')?;
            let v = p.peek_characters(3)?;
            if v[0] != 'ß' {
                return p.fail(&format!("unexpected character: '{}'", v[0]), ());
            }
            if v[1] != '京' {
                return p.fail(&format!("unexpected character: '{}'", v[1]), ());
            }
            if v[2] != '🦀' {
                return p.fail(&format!("unexpected character: '{}'", v[2]), ());
            }
            p.string("ß京🦀")?;
        }
        p.eof()
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}

#[test]
fn test_peek_invalid_chars() {
    let mut input = tiny_mixed_invalid_stream();
    let mut s = to_stream(&mut input);
    let parse = |p: &mut ByteStream| -> ParseResult<()> {

        p.character('@')?;

        let v = p.peek_characters(3)?;
        if v[0] != 'ß' {
           return p.fail(&format!("unexpected character: '{}'", v[0]), ());
        }
        if v[1] != '京' {
           return p.fail(&format!("unexpected character: '{}'", v[1]), ());
        }
        if v[2] != '🦀' {
           return p.fail(&format!("unexpected character: '{}'", v[2]), ());
        }
        p.string("ß京🦀")?;

        let _ = match p.peek_characters(3) {
            Ok(v) => return p.fail(&format!("unexpected character sequence: '{:?}'", v), ()),
            Err(e) if e.is_utf8_error() => true,
            Err(e) => return p.fail(&format!("unexpected error: '{:?}'", e), ()),
        };

        p.byte(255)?;

        let v = p.peek_characters(3)?;
        if v[0] != '@' {
           return p.fail(&format!("unexpected character: '{}'", v[0]), ());
        }
        if v[1] != 'ß' {
           return p.fail(&format!("unexpected character: '{}'", v[1]), ());
        }
        if v[2] != '京' {
           return p.fail(&format!("unexpected character: '{}'", v[2]), ());
        }
        p.string("@ß京🦀")?;

        p.byte(255)?;
        p.eof()
    };
    assert!(match parse(&mut s) {
        Ok(()) => true,
        Err(e) => panic!("unexpected error: {:?}", e),
    });
}
