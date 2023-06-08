# Pacosso - a kind of streaming parser combinator framework for Rust

_Pacosso_ is a framework for rapid parser development.
It does not aim at building high-performance parsers -
other frameworks are much more suitable for that -
but rather at easy development for rapid prototyping
and projects with moderate performance requirements.

Different from other streaming parser libraries,
_pacosso_ manages the incoming stream internally.
The feature is intended to make writing parsers
as easy as possible.
_Pacosso_ is able to handle any reader including
in-memory buffers and strings, files, sockets and
IO-chains combining such readers.

Documentation is available [here].

[Jsosso] is a JSON parser that demonstrates the framework.
It contains demo programs, benchmarks and more documentation.

[here]: https://docs.rs/pacosso/0.2.4/pacosso/
[Jsosso]: https://github.com/toschoo/jsosso

