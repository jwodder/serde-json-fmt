use serde::Serialize;
use serde_json::ser::Formatter;
use serde_json::Serializer;
use smartstring::alias::CompactString;
use std::fmt;
use std::io::{self, Write};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
// TODO: Rename to "JSONOptions"?
pub struct JSONFormat {
    indent: Option<CompactString>,
    comma: CompactString,
    colon: CompactString,
    ascii: bool,
}

impl JSONFormat {
    // Uses serde-json's default/"compact" formatting
    // Note that this format omits spaces from the comma & colon separators
    pub fn new() -> Self {
        JSONFormat {
            indent: None,
            comma: ",".into(),
            colon: ":".into(),
            ascii: false,
        }
    }

    // Uses serde-json's "pretty" formatting
    pub fn pretty() -> Self {
        JSONFormat {
            indent: Some("  ".into()),
            comma: ", ".into(),
            colon: ": ".into(),
            ascii: false,
        }
    }

    pub fn ascii(mut self, flag: bool) -> Self {
        self.ascii = flag;
        self
    }

    // Set the comma/list item separator
    // Errors when given an invalid separator (i.e., one that is not of the
    // form `/\A\s*,\s*\Z/`)
    pub fn comma<S: AsRef<str>>(mut self, s: S) -> Result<Self, Error> {
        self.comma = validate_string(s, Some(','))?;
        Ok(self)
    }

    // Set the colon/key-value separator
    // Errors when given an invalid separator (i.e., one that is not of the
    // form `/\A\s*:\s*\Z/`)
    pub fn colon<S: AsRef<str>>(mut self, s: S) -> Result<Self, Error> {
        self.colon = validate_string(s, Some(':'))?;
        Ok(self)
    }

    pub fn spaced_separators(self, flag: bool) -> Self {
        if flag {
            self.comma(", ").unwrap().colon(": ").unwrap()
        } else {
            self.comma(",").unwrap().colon(":").unwrap()
        }
    }

    // Sets the indentation
    //  - `None` means to not insert any newlines, while `Some("")` means to
    //    insert newlines but not indent.
    //  - Problem: passing `None` will require specifying the type of `S`;
    //    users should be advised to use `indent_width()` in this case instead
    //  - Errors if the string is not all JSON whitespace
    pub fn indent<S: AsRef<str>>(mut self, s: Option<S>) -> Result<Self, Error> {
        self.indent = s.map(|s| validate_string(s, None)).transpose()?;
        Ok(self)
    }

    pub fn indent_width(self, n: Option<usize>) -> Self {
        self.indent(n.map(|i| " ".repeat(i))).unwrap()
    }

    pub fn build(self) -> JSONFormatterOwned {
        JSONFormatterOwned::new(self)
    }

    pub fn as_formatter(&self) -> JSONFormatter<'_> {
        JSONFormatter::new(JSONFormatRef {
            indent: self.indent.as_ref().map(|s| s.as_bytes()),
            comma: self.comma.as_bytes(),
            colon: self.colon.as_bytes(),
            ascii: self.ascii,
        })
    }

    pub fn format_to_string<T: ?Sized + Serialize>(
        &self,
        value: &T,
    ) -> Result<String, serde_json::Error> {
        self.format_to_vec(value)
            .map(|v| String::from_utf8(v).unwrap())
    }

    pub fn format_to_writer<T: ?Sized + Serialize, W: Write>(
        &self,
        writer: W,
        value: &T,
    ) -> Result<(), serde_json::Error> {
        let mut ser = Serializer::with_formatter(writer, self.as_formatter());
        value.serialize(&mut ser)
    }

    pub fn format_to_vec<T: ?Sized + Serialize>(
        &self,
        value: &T,
    ) -> Result<Vec<u8>, serde_json::Error> {
        let mut vec = Vec::with_capacity(128);
        self.format_to_writer(&mut vec, value)?;
        Ok(vec)
    }
}

impl Default for JSONFormat {
    fn default() -> Self {
        JSONFormat::new()
    }
}

pub trait OptionsData {
    fn indent(&self) -> Option<&[u8]>;
    fn comma(&self) -> &[u8];
    fn colon(&self) -> &[u8];
    fn ascii(&self) -> bool;
}

impl OptionsData for JSONFormat {
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
pub struct JSONFormatRef<'a> {
    indent: Option<&'a [u8]>,
    comma: &'a [u8],
    colon: &'a [u8],
    ascii: bool,
}

impl<'a> OptionsData for JSONFormatRef<'a> {
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
pub struct JSONFormatterBase<O> {
    indent_level: usize,
    indent_next: bool,
    options: O,
}

impl<O: OptionsData> JSONFormatterBase<O> {
    fn new(options: O) -> Self {
        JSONFormatterBase {
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

impl<O: OptionsData> Formatter for JSONFormatterBase<O> {
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

    fn begin_object_value<W: ?Sized + io::Write>(&mut self, writer: &mut W) -> io::Result<()> {
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

pub type JSONFormatterOwned = JSONFormatterBase<JSONFormat>;
pub type JSONFormatter<'a> = JSONFormatterBase<JSONFormatRef<'a>>;

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
// TODO: Rename to something like "ArgumentError"/"ParameterError"
pub enum Error {
    // a string parameter contained an unexpected character
    InvalidCharacter(char),
    // a `comma` or `colon` parameter is missing the comma/colon
    MissingSeparator(char),
    // a `comma` or `colon` parameter has multiple commas/colons
    MultipleSeparators(char),
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        use Error::*;
        match self {
            InvalidCharacter(c) => write!(f, "String contains unexpected character {c:?}"),
            MissingSeparator(c) => write!(f, "No occurrence of {c:?} found in string"),
            MultipleSeparators(c) => write!(f, "Multiple occurrences of {c:?} found in string"),
        }
    }
}

impl std::error::Error for Error {}

fn validate_string<S: AsRef<str>>(s: S, sep: Option<char>) -> Result<CompactString, Error> {
    let s = s.as_ref();
    let mut seen_sep = false;
    for ch in s.chars() {
        match (sep, ch) {
            (Some(sep_), ch) if sep_ == ch => {
                if std::mem::replace(&mut seen_sep, true) {
                    return Err(Error::MultipleSeparators(sep_));
                }
            }
            // RFC 8259, section 2
            (_, ' ' | '\t' | '\n' | '\r') => (),
            (_, ch) => return Err(Error::InvalidCharacter(ch)),
        }
    }
    if let Some(sep_) = sep {
        if !seen_sep {
            return Err(Error::MissingSeparator(sep_));
        }
    }
    Ok(s.into())
}
