//! The `serde-json-fmt` crate lets you create custom [`serde_json`] formatters
//! with the indentation, separators, and ASCII requirements of your choice.
//!
//! `serde_json` itself only directly provides the ability to produce JSON in
//! either "compact" form or "pretty" form, with the only customizable aspect
//! being the string used for pretty indentation.  `serde-json-fmt` complements
//! `serde_json` to let you also customize the whitespace around commas &
//! colons and whether to escape non-ASCII characters.
//!
//! # Examples
//!
//! Say you want to serialize a value in one-line "compact" form, but you want
//! a space after each colon & comma, something that `serde_json`'s compact
//! form doesn't do.  `serde-json-fmt` lets you do that:
//!
//! ```
//! use serde_json::json;
//! use serde_json_fmt::JsonFormat;
//!
//! let value = json!({
//!     "colors": ["red", "blue", "taupe"],
//!     "sub": {
//!         "name": "Foo",
//!         "on": true,
//!         "size": 17
//!     }
//! });
//!
//! let s = JsonFormat::new()
//!     .comma(", ")
//!     .unwrap()
//!     .colon(": ")
//!     .unwrap()
//!     .format_to_string(&value)
//!     .unwrap();
//!
//! assert_eq!(
//!     s,
//!     r#"{"colors": ["red", "blue", "taupe"], "sub": {"name": "Foo", "on": true, "size": 17}}"#
//! );
//! ```
//!
//! Say you want to format a value in multiline "pretty" form, but using
//! four-space indents and with all non-ASCII characters encoded as `\uXXXX`
//! escape sequences.  `serde-json-fmt` lets you do that:
//!
//! ```
//! use serde_json::json;
//! use serde_json_fmt::JsonFormat;
//!
//! let value = json!({
//!     "emojis": {
//!         "goat":"🐐",
//!         "pineapple": "🍍",
//!         "smile": "😀",
//!     },
//!     "greek": {
//!         "α": "alpha",
//!         "β": "beta",
//!         "γ": "gamma",
//!     }
//! });
//!
//! let s = JsonFormat::pretty()
//!     .indent_width(Some(4))
//!     .ascii(true)
//!     .format_to_string(&value)
//!     .unwrap();
//!
//! assert_eq!(s, r#"{
//!     "emojis": {
//!         "goat": "\ud83d\udc10",
//!         "pineapple": "\ud83c\udf4d",
//!         "smile": "\ud83d\ude00"
//!     },
//!     "greek": {
//!         "\u03b1": "alpha",
//!         "\u03b2": "beta",
//!         "\u03b3": "gamma"
//!     }
//! }"#);
//! ```

use serde::Serialize;
use serde_json::ser::Formatter;
use serde_json::Serializer;
use smartstring::alias::CompactString;
use std::fmt;
use std::io::{self, Write};

/// A [`Formatter`] builder for configuring JSON serialization options.
///
/// This type is the "entry point" to `serde-json-fmt`'s functionality.  To
/// perform custom-formatted JSON serialization, start by creating a
/// `JsonFormat` instance by calling either [`JsonFormat::new()`] or
/// [`JsonFormat::pretty()`], then call the various configuration methods as
/// desired, then either pass your [`serde::Serialize`] value to one of the
/// [`format_to_string()`][JsonFormat::format_to_string],
/// [`format_to_vec()`][JsonFormat::format_to_vec], and
/// [`format_to_writer()`][JsonFormat::format_to_writer] convenience methods or
/// else (for lower-level usage) call [`build()`][JsonFormat::build] or
/// [`as_formatter()`][JsonFormat::as_formatter] to acquire a
/// [`serde_json::ser::Formatter`] instance.
#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct JsonFormat {
    indent: Option<CompactString>,
    comma: CompactString,
    colon: CompactString,
    ascii: bool,
}

impl JsonFormat {
    /// Create a new `JsonFormat` instance that starts out configured to use
    /// `serde_json`'s "compact" format.  Specifically, the instance is
    /// configured as follows:
    ///
    /// - `indent(None)`
    /// - `comma(",")`
    /// - `colon(":")`
    /// - `ascii(false)`
    pub fn new() -> Self {
        JsonFormat {
            indent: None,
            comma: ",".into(),
            colon: ":".into(),
            ascii: false,
        }
    }

    /// Create a new `JsonFormat` instance that starts out configured to use
    /// `serde_json`'s "pretty" format.  Specifically, the instance is
    /// configured as follows:
    ///
    /// - `indent(Some("  "))` (two spaces)
    /// - `comma(",")`
    /// - `colon(": ")`
    /// - `ascii(false)`
    pub fn pretty() -> Self {
        JsonFormat {
            indent: Some("  ".into()),
            comma: ",".into(),
            colon: ": ".into(),
            ascii: false,
        }
    }

    /// Set whether non-ASCII characters in strings should be serialized as
    /// ASCII using `\uXXXX` escape sequences.  If `flag` is `true`, then all
    /// non-ASCII characters will be escaped; if `flag` is `false`, then
    /// non-ASCII characters will be serialized as themselves.
    pub fn ascii(mut self, flag: bool) -> Self {
        self.ascii = flag;
        self
    }

    /// Set the string to use as the item separator in lists & objects.
    ///
    /// `s` must contain exactly one comma (`,`) character; all other
    /// characters must be space characters, tabs, line feeds, and/or carriage
    /// returns.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `s` does not meet the above requirements.
    pub fn comma<S: AsRef<str>>(mut self, s: S) -> Result<Self, JsonSyntaxError> {
        self.comma = validate_string(s, Some(','))?;
        Ok(self)
    }

    /// Set the string to use as the key-value separator in objects.
    ///
    /// `s` must contain exactly one colon (`:`) character; all other
    /// characters must be space characters, tabs, line feeds, and/or carriage
    /// returns.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `s` does not meet the above requirements.
    pub fn colon<S: AsRef<str>>(mut self, s: S) -> Result<Self, JsonSyntaxError> {
        self.colon = validate_string(s, Some(':'))?;
        Ok(self)
    }

    /// Set the string used for indentation.
    ///
    /// If `s` is `None`, then no indentation or newlines will be inserted when
    /// serializing.  If `s` is `Some("")` (an empty string), then newlines
    /// will be inserted, but nothing will be indented.  If `s` contains any
    /// other string, the string must consist entirely of space characters,
    /// tabs, line feeds, and/or carriage returns.
    ///
    /// # Errors
    ///
    /// Returns `Err` if `s` contains a string that contains any character
    /// other than those listed above.
    pub fn indent<S: AsRef<str>>(mut self, s: Option<S>) -> Result<Self, JsonSyntaxError> {
        self.indent = s.map(|s| validate_string(s, None)).transpose()?;
        Ok(self)
    }

    /// Set the string used for indentation to the given number of spaces.
    ///
    /// This method is a convenience wrapper around
    /// [`indent()`][JsonFormat::indent] that calls it with a string consisting
    /// of the given number of space characters, or with `None` if `n` is
    /// `None`.
    pub fn indent_width(self, n: Option<usize>) -> Self {
        let Ok(me) = self.indent(n.map(|i| CompactString::from(" ").repeat(i))) else {
            unreachable!("repeated spaces should be valid indentation");
        };
        me
    }

    /// Format a [`serde::Serialize`] value to a [`String`] as JSON using the
    /// configured formatting options.
    ///
    /// # Errors
    ///
    /// Has the same error conditions as [`serde_json::to_string()`].
    pub fn format_to_string<T: ?Sized + Serialize>(
        &self,
        value: &T,
    ) -> Result<String, serde_json::Error> {
        let bytes = self.format_to_vec(value)?;
        let Ok(s) = String::from_utf8(bytes) else {
            unreachable!("serialized JSON should be valid UTF-8");
        };
        Ok(s)
    }

    /// Format a [`serde::Serialize`] value to a [`Vec<u8>`] as JSON using the
    /// configured formatting options.
    ///
    /// # Errors
    ///
    /// Has the same error conditions as [`serde_json::to_vec()`].
    pub fn format_to_vec<T: ?Sized + Serialize>(
        &self,
        value: &T,
    ) -> Result<Vec<u8>, serde_json::Error> {
        let mut vec = Vec::with_capacity(128);
        self.format_to_writer(&mut vec, value)?;
        Ok(vec)
    }

    /// Write a [`serde::Serialize`] value to a [`std::io::Write`] instance as
    /// JSON using the configured formatting options.
    ///
    /// # Errors
    ///
    /// Has the same error conditions as [`serde_json::to_writer()`].
    pub fn format_to_writer<T: ?Sized + Serialize, W: Write>(
        &self,
        writer: W,
        value: &T,
    ) -> Result<(), serde_json::Error> {
        let mut ser = Serializer::with_formatter(writer, self.as_formatter());
        value.serialize(&mut ser)
    }

    /// Consume the `JsonFormat` instance and return a
    /// [`serde_json::ser::Formatter`] instance.
    ///
    /// This is a low-level operation.  For most use cases, using one of the
    /// [`format_to_string()`][JsonFormat::format_to_string],
    /// [`format_to_vec()`][JsonFormat::format_to_vec], and
    /// [`format_to_writer()`][JsonFormat::format_to_writer] convenience
    /// methods is recommended.
    pub fn build(self) -> JsonFormatter {
        JsonFormatter::new(self)
    }

    /// Return a [`serde_json::ser::Formatter`] instance that borrows data from
    /// the `JsonFormat` instance.
    ///
    /// This is a low-level operation.  For most use cases, using one of the
    /// [`format_to_string()`][JsonFormat::format_to_string],
    /// [`format_to_vec()`][JsonFormat::format_to_vec], and
    /// [`format_to_writer()`][JsonFormat::format_to_writer] convenience
    /// methods is recommended.
    ///
    /// Unlike [`build()`][JsonFormat::build], this method makes it possible to
    /// create multiple `Formatter`s from a single `JsonFormat` instance.
    pub fn as_formatter(&self) -> JsonFrmtr<'_> {
        JsonFrmtr::new(internal::JsonFmt {
            indent: self.indent.as_ref().map(|s| s.as_bytes()),
            comma: self.comma.as_bytes(),
            colon: self.colon.as_bytes(),
            ascii: self.ascii,
        })
    }
}

impl Default for JsonFormat {
    /// Equivalent to [`JsonFormat::new()`]
    fn default() -> Self {
        JsonFormat::new()
    }
}

// Workaround from <https://github.com/rust-lang/rust/issues/34537> for making
// types in public interfaces private
mod internal {
    use super::*;

    pub trait OptionsData {
        fn indent(&self) -> Option<&[u8]>;
        fn comma(&self) -> &[u8];
        fn colon(&self) -> &[u8];
        fn ascii(&self) -> bool;
    }

    impl OptionsData for JsonFormat {
        fn indent(&self) -> Option<&[u8]> {
            self.indent.as_ref().map(|s| s.as_bytes())
        }

        fn comma(&self) -> &[u8] {
            self.comma.as_bytes()
        }

        fn colon(&self) -> &[u8] {
            self.colon.as_bytes()
        }

        fn ascii(&self) -> bool {
            self.ascii
        }
    }

    #[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
    pub struct JsonFmt<'a> {
        pub indent: Option<&'a [u8]>,
        pub comma: &'a [u8],
        pub colon: &'a [u8],
        pub ascii: bool,
    }

    impl OptionsData for JsonFmt<'_> {
        fn indent(&self) -> Option<&[u8]> {
            self.indent
        }

        fn comma(&self) -> &[u8] {
            self.comma
        }

        fn colon(&self) -> &[u8] {
            self.colon
        }

        fn ascii(&self) -> bool {
            self.ascii
        }
    }

    #[derive(Clone, Debug, Eq, Hash, PartialEq)]
    pub struct JsonFormatterBase<O> {
        indent_level: usize,
        indent_next: bool,
        options: O,
    }

    impl<O: OptionsData> JsonFormatterBase<O> {
        pub fn new(options: O) -> Self {
            JsonFormatterBase {
                indent_level: 0,
                indent_next: false,
                options,
            }
        }

        fn print_indent<W: ?Sized + Write>(&self, writer: &mut W) -> io::Result<()> {
            if let Some(indent) = self.options.indent() {
                writer.write_all(b"\n")?;
                for _ in 0..self.indent_level {
                    writer.write_all(indent)?;
                }
            }
            Ok(())
        }
    }

    impl<O: OptionsData> Formatter for JsonFormatterBase<O> {
        fn begin_array<W: ?Sized + Write>(&mut self, writer: &mut W) -> io::Result<()> {
            self.indent_level += 1;
            self.indent_next = false;
            writer.write_all(b"[")
        }

        fn begin_array_value<W: ?Sized + Write>(
            &mut self,
            writer: &mut W,
            first: bool,
        ) -> io::Result<()> {
            if !first {
                writer.write_all(self.options.comma())?;
            }
            self.print_indent(writer)
        }

        fn end_array_value<W: ?Sized + Write>(&mut self, _writer: &mut W) -> io::Result<()> {
            self.indent_next = true;
            Ok(())
        }

        fn end_array<W: ?Sized + Write>(&mut self, writer: &mut W) -> io::Result<()> {
            self.indent_level -= 1;
            if self.indent_next {
                self.print_indent(writer)?;
            }
            writer.write_all(b"]")
        }

        fn begin_object<W: ?Sized + Write>(&mut self, writer: &mut W) -> io::Result<()> {
            self.indent_level += 1;
            self.indent_next = false;
            writer.write_all(b"{")
        }

        fn begin_object_key<W: ?Sized + Write>(
            &mut self,
            writer: &mut W,
            first: bool,
        ) -> io::Result<()> {
            if !first {
                writer.write_all(self.options.comma())?;
            }
            self.print_indent(writer)
        }

        fn begin_object_value<W: ?Sized + Write>(&mut self, writer: &mut W) -> io::Result<()> {
            writer.write_all(self.options.colon())
        }

        fn end_object_value<W: ?Sized + Write>(&mut self, _writer: &mut W) -> io::Result<()> {
            self.indent_next = true;
            Ok(())
        }

        fn end_object<W: ?Sized + Write>(&mut self, writer: &mut W) -> io::Result<()> {
            self.indent_level -= 1;
            if self.indent_next {
                self.print_indent(writer)?;
            }
            writer.write_all(b"}")
        }

        fn write_string_fragment<W: ?Sized + Write>(
            &mut self,
            writer: &mut W,
            fragment: &str,
        ) -> io::Result<()> {
            for ch in fragment.chars() {
                if !self.options.ascii() || ch.is_ascii() {
                    writer.write_all(ch.encode_utf8(&mut [0; 4]).as_bytes())?;
                } else {
                    for surrogate in ch.encode_utf16(&mut [0; 2]) {
                        write!(writer, "\\u{surrogate:04x}")?;
                    }
                }
            }
            Ok(())
        }
    }
}

/// A [`serde_json::ser::Formatter`] type that owns its data.
///
/// Instances of this type are acquired by calling [`JsonFormat::build()`].
pub type JsonFormatter = internal::JsonFormatterBase<JsonFormat>;

/// A [`serde_json::ser::Formatter`] type that borrows its data from a
/// [`JsonFormat`].
///
/// Instances of this type are acquired by calling
/// [`JsonFormat::as_formatter()`].
pub type JsonFrmtr<'a> = internal::JsonFormatterBase<internal::JsonFmt<'a>>;

/// Error returned when an invalid string is passed to certain [`JsonFormat`]
/// methods.
#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub enum JsonSyntaxError {
    /// Returned when the given string contains an invalid/unexpected
    /// character.  Contains the character in question.
    InvalidCharacter(char),

    /// Retured when a string passed to [`JsonFormat::comma()`] or
    /// [`JsonFormat::colon()`] does not contain a comma or colon,
    /// respectively.  Contains a comma or colon as appropriate.
    MissingSeparator(char),

    /// Retured when a string passed to [`JsonFormat::comma()`] or
    /// [`JsonFormat::colon()`] contains more than one comma or colon,
    /// respectively.  Contains a comma or colon as appropriate.
    MultipleSeparators(char),
}

impl fmt::Display for JsonSyntaxError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use JsonSyntaxError::*;
        match self {
            InvalidCharacter(c) => write!(f, "string contains unexpected character {c:?}"),
            MissingSeparator(c) => write!(f, "no occurrence of {c:?} found in string"),
            MultipleSeparators(c) => write!(f, "multiple occurrences of {c:?} found in string"),
        }
    }
}

impl std::error::Error for JsonSyntaxError {}

fn validate_string<S: AsRef<str>>(
    s: S,
    sep: Option<char>,
) -> Result<CompactString, JsonSyntaxError> {
    let s = s.as_ref();
    let mut seen_sep = false;
    for ch in s.chars() {
        match (sep, ch) {
            (Some(sep_), ch) if sep_ == ch => {
                if std::mem::replace(&mut seen_sep, true) {
                    return Err(JsonSyntaxError::MultipleSeparators(sep_));
                }
            }
            // RFC 8259, section 2
            (_, ' ' | '\t' | '\n' | '\r') => (),
            (_, ch) => return Err(JsonSyntaxError::InvalidCharacter(ch)),
        }
    }
    if let Some(sep_) = sep {
        if !seen_sep {
            return Err(JsonSyntaxError::MissingSeparator(sep_));
        }
    }
    Ok(s.into())
}

#[cfg(test)]
mod tests {
    use super::*;
    use indoc::indoc;
    use rstest::rstest;
    use serde_json::json;

    #[rstest]
    #[case("?", Ok("?".into()))]
    #[case(" ?", Ok(" ?".into()))]
    #[case("? ", Ok("? ".into()))]
    #[case("  ? ", Ok("  ? ".into()))]
    #[case(" \t?\r\n", Ok(" \t?\r\n".into()))]
    #[case("", Err(JsonSyntaxError::MissingSeparator('?')))]
    #[case(" ", Err(JsonSyntaxError::MissingSeparator('?')))]
    #[case("??", Err(JsonSyntaxError::MultipleSeparators('?')))]
    #[case("? ?", Err(JsonSyntaxError::MultipleSeparators('?')))]
    #[case("\x0C", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case("\x0B", Err(JsonSyntaxError::InvalidCharacter('\x0B')))]
    #[case("\u{A0}", Err(JsonSyntaxError::InvalidCharacter('\u{A0}')))]
    #[case("\u{85}", Err(JsonSyntaxError::InvalidCharacter('\u{85}')))]
    #[case("\u{1680}", Err(JsonSyntaxError::InvalidCharacter('\u{1680}')))]
    #[case("\u{180E}", Err(JsonSyntaxError::InvalidCharacter('\u{180E}')))]
    #[case("\u{2000}", Err(JsonSyntaxError::InvalidCharacter('\u{2000}')))]
    #[case("\u{2001}", Err(JsonSyntaxError::InvalidCharacter('\u{2001}')))]
    #[case("\u{2002}", Err(JsonSyntaxError::InvalidCharacter('\u{2002}')))]
    #[case("\u{2003}", Err(JsonSyntaxError::InvalidCharacter('\u{2003}')))]
    #[case("\u{2004}", Err(JsonSyntaxError::InvalidCharacter('\u{2004}')))]
    #[case("\u{2005}", Err(JsonSyntaxError::InvalidCharacter('\u{2005}')))]
    #[case("\u{2006}", Err(JsonSyntaxError::InvalidCharacter('\u{2006}')))]
    #[case("\u{2007}", Err(JsonSyntaxError::InvalidCharacter('\u{2007}')))]
    #[case("\u{2008}", Err(JsonSyntaxError::InvalidCharacter('\u{2008}')))]
    #[case("\u{2009}", Err(JsonSyntaxError::InvalidCharacter('\u{2009}')))]
    #[case("\u{200A}", Err(JsonSyntaxError::InvalidCharacter('\u{200A}')))]
    #[case("\u{200B}", Err(JsonSyntaxError::InvalidCharacter('\u{200B}')))]
    #[case("\u{200C}", Err(JsonSyntaxError::InvalidCharacter('\u{200C}')))]
    #[case("\u{200D}", Err(JsonSyntaxError::InvalidCharacter('\u{200D}')))]
    #[case("\u{2028}", Err(JsonSyntaxError::InvalidCharacter('\u{2028}')))]
    #[case("\u{2029}", Err(JsonSyntaxError::InvalidCharacter('\u{2029}')))]
    #[case("\u{202F}", Err(JsonSyntaxError::InvalidCharacter('\u{202F}')))]
    #[case("\u{205F}", Err(JsonSyntaxError::InvalidCharacter('\u{205F}')))]
    #[case("\u{2060}", Err(JsonSyntaxError::InvalidCharacter('\u{2060}')))]
    #[case("\u{3000}", Err(JsonSyntaxError::InvalidCharacter('\u{3000}')))]
    #[case("\u{FEFF}", Err(JsonSyntaxError::InvalidCharacter('\u{FEFF}')))]
    #[case("\x0C?", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case("?\x0C", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case("?\x0C?", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case("??\x0C", Err(JsonSyntaxError::MultipleSeparators('?')))]
    #[case(".", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case(".?", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case("?.", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case("?.?", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case("??.", Err(JsonSyntaxError::MultipleSeparators('?')))]
    #[case("☃", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case("☃?", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case("?☃", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case("?☃?", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case("??☃", Err(JsonSyntaxError::MultipleSeparators('?')))]
    fn test_validate_string_sep(
        #[case] s: &str,
        #[case] r: Result<CompactString, JsonSyntaxError>,
    ) {
        assert_eq!(validate_string(s, Some('?')), r);
    }

    #[rstest]
    #[case("", Ok("".into()))]
    #[case(" ", Ok(" ".into()))]
    #[case("    ", Ok("    ".into()))]
    #[case(" \t\r\n", Ok(" \t\r\n".into()))]
    #[case("?", Err(JsonSyntaxError::InvalidCharacter('?')))]
    #[case(" ?", Err(JsonSyntaxError::InvalidCharacter('?')))]
    #[case("? ", Err(JsonSyntaxError::InvalidCharacter('?')))]
    #[case("  ? ", Err(JsonSyntaxError::InvalidCharacter('?')))]
    #[case("??", Err(JsonSyntaxError::InvalidCharacter('?')))]
    #[case("\x0C", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case("\x0B", Err(JsonSyntaxError::InvalidCharacter('\x0B')))]
    #[case("\u{A0}", Err(JsonSyntaxError::InvalidCharacter('\u{A0}')))]
    #[case("\u{85}", Err(JsonSyntaxError::InvalidCharacter('\u{85}')))]
    #[case("\u{1680}", Err(JsonSyntaxError::InvalidCharacter('\u{1680}')))]
    #[case("\u{180E}", Err(JsonSyntaxError::InvalidCharacter('\u{180E}')))]
    #[case("\u{2000}", Err(JsonSyntaxError::InvalidCharacter('\u{2000}')))]
    #[case("\u{2001}", Err(JsonSyntaxError::InvalidCharacter('\u{2001}')))]
    #[case("\u{2002}", Err(JsonSyntaxError::InvalidCharacter('\u{2002}')))]
    #[case("\u{2003}", Err(JsonSyntaxError::InvalidCharacter('\u{2003}')))]
    #[case("\u{2004}", Err(JsonSyntaxError::InvalidCharacter('\u{2004}')))]
    #[case("\u{2005}", Err(JsonSyntaxError::InvalidCharacter('\u{2005}')))]
    #[case("\u{2006}", Err(JsonSyntaxError::InvalidCharacter('\u{2006}')))]
    #[case("\u{2007}", Err(JsonSyntaxError::InvalidCharacter('\u{2007}')))]
    #[case("\u{2008}", Err(JsonSyntaxError::InvalidCharacter('\u{2008}')))]
    #[case("\u{2009}", Err(JsonSyntaxError::InvalidCharacter('\u{2009}')))]
    #[case("\u{200A}", Err(JsonSyntaxError::InvalidCharacter('\u{200A}')))]
    #[case("\u{200B}", Err(JsonSyntaxError::InvalidCharacter('\u{200B}')))]
    #[case("\u{200C}", Err(JsonSyntaxError::InvalidCharacter('\u{200C}')))]
    #[case("\u{200D}", Err(JsonSyntaxError::InvalidCharacter('\u{200D}')))]
    #[case("\u{2028}", Err(JsonSyntaxError::InvalidCharacter('\u{2028}')))]
    #[case("\u{2029}", Err(JsonSyntaxError::InvalidCharacter('\u{2029}')))]
    #[case("\u{202F}", Err(JsonSyntaxError::InvalidCharacter('\u{202F}')))]
    #[case("\u{205F}", Err(JsonSyntaxError::InvalidCharacter('\u{205F}')))]
    #[case("\u{2060}", Err(JsonSyntaxError::InvalidCharacter('\u{2060}')))]
    #[case("\u{3000}", Err(JsonSyntaxError::InvalidCharacter('\u{3000}')))]
    #[case("\u{FEFF}", Err(JsonSyntaxError::InvalidCharacter('\u{FEFF}')))]
    #[case("\x0C ", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case(" \x0C", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case(" \x0C ", Err(JsonSyntaxError::InvalidCharacter('\x0C')))]
    #[case(".", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case(". ", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case(" .", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case(" . ", Err(JsonSyntaxError::InvalidCharacter('.')))]
    #[case("☃", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case("☃ ", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case(" ☃", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    #[case(" ☃ ", Err(JsonSyntaxError::InvalidCharacter('☃')))]
    fn test_validate_string_no_sep(
        #[case] s: &str,
        #[case] r: Result<CompactString, JsonSyntaxError>,
    ) {
        assert_eq!(validate_string(s, None), r);
    }

    #[test]
    fn test_format_default() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        let s = JsonFormat::new().format_to_string(&value).unwrap();
        assert_eq!(
            s,
            r#"{"colors":["red","blue","taupe"],"sub":{"name":"Foo","on":true,"size":17}}"#
        );
    }

    #[test]
    fn test_format_pretty() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        let s = JsonFormat::pretty().format_to_string(&value).unwrap();
        assert_eq!(
            s,
            indoc! {r#"{
              "colors": [
                "red",
                "blue",
                "taupe"
              ],
              "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
              }
            }"#}
        );
    }

    #[test]
    fn test_format_default_is_new() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        assert_eq!(
            JsonFormat::new().format_to_string(&value).unwrap(),
            JsonFormat::default().format_to_string(&value).unwrap(),
        );
    }

    #[test]
    fn test_format_default_matches_serde_json() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        assert_eq!(
            JsonFormat::new().format_to_string(&value).unwrap(),
            serde_json::to_string(&value).unwrap(),
        );
    }

    #[test]
    fn test_format_pretty_matches_serde_json() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        assert_eq!(
            JsonFormat::pretty().format_to_string(&value).unwrap(),
            serde_json::to_string_pretty(&value).unwrap(),
        );
    }

    #[test]
    fn test_format_pretty_complicated() {
        let value = json!({
            "colors": [
                "red",
                "blue",
                "taupe"
            ],
            "sampler": {
                "empty_list": [],
                "empty_object": {},
                "nested": {
                    "list": [
                        1,
                        {
                            "strange": "charmed",
                            "truth": "beauty",
                            "up": "down"
                        },
                        3
                    ],
                },
                "null": null,
                "singleton_list": [
                    42
                ],
                "singleton_object": {
                    "key": "value"
                }
            },
            "sub": {
                "name": "Foo",
                "size": 17,
                "on": true
            }
        });
        let s = JsonFormat::pretty().format_to_string(&value).unwrap();
        assert_eq!(
            s,
            indoc! {r#"{
              "colors": [
                "red",
                "blue",
                "taupe"
              ],
              "sampler": {
                "empty_list": [],
                "empty_object": {},
                "nested": {
                  "list": [
                    1,
                    {
                      "strange": "charmed",
                      "truth": "beauty",
                      "up": "down"
                    },
                    3
                  ]
                },
                "null": null,
                "singleton_list": [
                  42
                ],
                "singleton_object": {
                  "key": "value"
                }
              },
              "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
              }
            }"#}
        );
    }

    #[test]
    fn test_format_pretty_complicated_indent_4() {
        let value = json!({
            "colors": [
                "red",
                "blue",
                "taupe"
            ],
            "sampler": {
                "empty_list": [],
                "empty_object": {},
                "nested": {
                    "list": [
                        1,
                        {
                            "strange": "charmed",
                            "truth": "beauty",
                            "up": "down"
                        },
                        3
                    ],
                },
                "null": null,
                "singleton_list": [
                    42
                ],
                "singleton_object": {
                    "key": "value"
                }
            },
            "sub": {
                "name": "Foo",
                "size": 17,
                "on": true
            }
        });
        let s = JsonFormat::pretty()
            .indent_width(Some(4))
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            indoc! {r#"{
                "colors": [
                    "red",
                    "blue",
                    "taupe"
                ],
                "sampler": {
                    "empty_list": [],
                    "empty_object": {},
                    "nested": {
                        "list": [
                            1,
                            {
                                "strange": "charmed",
                                "truth": "beauty",
                                "up": "down"
                            },
                            3
                        ]
                    },
                    "null": null,
                    "singleton_list": [
                        42
                    ],
                    "singleton_object": {
                        "key": "value"
                    }
                },
                "sub": {
                    "name": "Foo",
                    "on": true,
                    "size": 17
                }
            }"#}
        );
    }

    #[test]
    fn test_format_pretty_empty_indent() {
        let value = json!({
            "nested": {
                "list": [
                    1,
                    {
                        "strange": "charmed",
                        "truth": "beauty",
                        "up": "down"
                    },
                    3
                ]
            }
        });
        let s = JsonFormat::pretty()
            .indent(Some(""))
            .unwrap()
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            indoc! {r#"{
            "nested": {
            "list": [
            1,
            {
            "strange": "charmed",
            "truth": "beauty",
            "up": "down"
            },
            3
            ]
            }
            }"#}
        );
    }

    #[test]
    fn test_format_pretty_zero_indent_width() {
        let value = json!({
            "nested": {
                "list": [
                    1,
                    {
                        "strange": "charmed",
                        "truth": "beauty",
                        "up": "down"
                    },
                    3
                ]
            }
        });
        let s = JsonFormat::pretty()
            .indent_width(Some(0))
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            indoc! {r#"{
            "nested": {
            "list": [
            1,
            {
            "strange": "charmed",
            "truth": "beauty",
            "up": "down"
            },
            3
            ]
            }
            }"#}
        );
    }

    #[test]
    fn test_format_pretty_tab_indent() {
        let value = json!({
            "nested": {
                "list": [
                    1,
                    {
                        "strange": "charmed",
                        "truth": "beauty",
                        "up": "down"
                    },
                    3
                ]
            }
        });
        let s = JsonFormat::pretty()
            .indent(Some("\t"))
            .unwrap()
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            indoc! {"{
            \t\"nested\": {
            \t\t\"list\": [
            \t\t\t1,
            \t\t\t{
            \t\t\t\t\"strange\": \"charmed\",
            \t\t\t\t\"truth\": \"beauty\",
            \t\t\t\t\"up\": \"down\"
            \t\t\t},
            \t\t\t3
            \t\t]
            \t}
            }"}
        );
    }

    #[test]
    fn test_format_spaced_separators() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        let s = JsonFormat::new()
            .comma(", ")
            .unwrap()
            .colon(": ")
            .unwrap()
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            r#"{"colors": ["red", "blue", "taupe"], "sub": {"name": "Foo", "on": true, "size": 17}}"#
        );
    }

    #[test]
    fn test_format_weird_separators() {
        let value = json!({
            "colors": ["red", "blue", "taupe"],
            "sub": {
                "name": "Foo",
                "on": true,
                "size": 17
            }
        });
        let s = JsonFormat::new()
            .comma("\n,")
            .unwrap()
            .colon("\t:\t")
            .unwrap()
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            "{\"colors\"\t:\t[\"red\"\n,\"blue\"\n,\"taupe\"]\n,\"sub\"\t:\t{\"name\"\t:\t\"Foo\"\n,\"on\"\t:\ttrue\n,\"size\"\t:\t17}}"
        );
    }

    #[test]
    fn test_format_unicode() {
        let value = json!({
            "föö": "snow☃man",
            "\u{1F410}": "\u{1F600}",
        });
        let s = JsonFormat::new().format_to_string(&value).unwrap();
        assert_eq!(s, "{\"föö\":\"snow☃man\",\"\u{1F410}\":\"\u{1F600}\"}");
    }

    #[test]
    fn test_format_unicode_in_ascii() {
        let value = json!({
            "föö": "snow☃man",
            "\u{1F410}": "\u{1F600}",
        });
        let s = JsonFormat::new()
            .ascii(true)
            .format_to_string(&value)
            .unwrap();
        assert_eq!(
            s,
            r#"{"f\u00f6\u00f6":"snow\u2603man","\ud83d\udc10":"\ud83d\ude00"}"#
        );
    }

    #[test]
    fn test_format_top_level_array() {
        let value = json!(["apple", ["banana"], {"grape": "raisin"}]);
        let s = JsonFormat::new().format_to_string(&value).unwrap();
        assert_eq!(s, r#"["apple",["banana"],{"grape":"raisin"}]"#);
    }

    #[test]
    fn test_format_top_level_array_pretty() {
        let value = json!(["apple", ["banana"], {"grape": "raisin"}]);
        let s = JsonFormat::pretty().format_to_string(&value).unwrap();
        assert_eq!(
            s,
            indoc! {r#"[
              "apple",
              [
                "banana"
              ],
              {
                "grape": "raisin"
              }
            ]"#}
        );
    }

    #[test]
    fn test_format_top_level_int() {
        let s = JsonFormat::new().format_to_string(&42).unwrap();
        assert_eq!(s, "42");
    }

    #[test]
    fn test_format_top_level_int_pretty() {
        let s = JsonFormat::pretty().format_to_string(&42).unwrap();
        assert_eq!(s, "42");
    }

    #[test]
    fn test_format_top_level_float() {
        let s = JsonFormat::new().format_to_string(&6.022).unwrap();
        assert_eq!(s, "6.022");
    }

    #[test]
    fn test_format_top_level_float_pretty() {
        let s = JsonFormat::pretty().format_to_string(&6.022).unwrap();
        assert_eq!(s, "6.022");
    }

    #[test]
    fn test_format_top_level_string() {
        let s = JsonFormat::new().format_to_string("foo").unwrap();
        assert_eq!(s, r#""foo""#);
    }

    #[test]
    fn test_format_top_level_string_pretty() {
        let s = JsonFormat::pretty().format_to_string("foo").unwrap();
        assert_eq!(s, r#""foo""#);
    }

    #[test]
    fn test_format_top_level_bool() {
        let s = JsonFormat::new().format_to_string(&true).unwrap();
        assert_eq!(s, "true");
    }

    #[test]
    fn test_format_top_level_bool_pretty() {
        let s = JsonFormat::pretty().format_to_string(&true).unwrap();
        assert_eq!(s, "true");
    }

    #[test]
    fn test_format_top_level_null() {
        let value = json!(null);
        let s = JsonFormat::new().format_to_string(&value).unwrap();
        assert_eq!(s, "null");
    }

    #[test]
    fn test_format_top_level_null_pretty() {
        let value = json!(null);
        let s = JsonFormat::pretty().format_to_string(&value).unwrap();
        assert_eq!(s, "null");
    }

    #[test]
    fn test_display_invalid_character() {
        let e = JsonSyntaxError::InvalidCharacter('ö');
        assert_eq!(e.to_string(), "string contains unexpected character 'ö'");
    }

    #[test]
    fn test_display_missing_separator() {
        let e = JsonSyntaxError::MissingSeparator('?');
        assert_eq!(e.to_string(), "no occurrence of '?' found in string");
    }

    #[test]
    fn test_display_multiple_separators() {
        let e = JsonSyntaxError::MultipleSeparators('?');
        assert_eq!(e.to_string(), "multiple occurrences of '?' found in string");
    }
}
