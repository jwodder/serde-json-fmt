use smartstring::smartstring;
use serde::Serialize;
use std::io::Write;
use serde_json::ser::Formatter;
use std::fmt;

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
// TODO: Rename to something with "Builder" in its name?
pub struct JSONFormat {
    indent: Option<smartstring>,
    comma: smartstring,
    colon: smartstring,
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
        todo!()
    }

    // Set the colon/key-value separator
    // Errors when given an invalid separator (i.e., one that is not of the
    // form `/\A\s*:\s*\Z/`)
    pub fn colon<S: AsRef<str>>(mut self, s: S) -> Result<Self, Error> {
        todo!()
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
        todo!()
    }

    pub fn indent_width(self, n: Option<usize>) -> Self {
        self.indent(n.map(|i| " ".repeat(i))).unwrap()
    }

    pub fn build(self) -> JSONFormatterOwned {
        JSONFormatterOwned {
            indent: self.indent,
            comma: self.comma,
            colon: self.colon,
            ascii: self.ascii,
        }
    }

    pub fn as_formatter(&self) -> JSONFormatter<'_> {
        JSONFormatter {
            indent: self.indent.as_ref().map(|s| s.as_bytes()),
            comma: self.comma.as_bytes(),
            colon: self.colon.as_bytes(),
            ascii: self.ascii,
        }
    }

    pub fn format_to_string<T: ?Sized + Serialize>(&self, value: &T) -> Result<String, serde_json::Error> {
        self.format_to_vec(value)?.map(String::from_utf8)
    }

    pub fn format_to_writer<T: ?Sized + Serialize, W: Write>(&self, writer: W, value: &T) -> Result<(), serde_json::Error> {
        let ser = Serializer::with_formatter(writer, self.as_formatter());
        value.serialize(ser)
    }

    pub fn format_to_vec<T: ?Sized + Serialize>(&self, value: &T) -> Result<Vec<u8>, serde_json::Error> {
        let mut vec = Vec::with_capacity(128);
        self.format_to_writer(&mut writer, value)?;
        Ok(vec)
    }
}

impl Default for JSONFormat {
    fn default() -> Self {
        JSONFormat::new()
    }
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct JSONFormatterOwned {
    ???
}

impl Formatter for JSONFormatterOwned {
    ???
}

#[derive(Clone, Copy, Debug, Eq, Hash, PartialEq)]
pub struct JSONFormatter<'a> {
    ???
}

impl<'a> Formatter for JSONFormatter<'a> {
    ???
}

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
        todo!()
    }
}

impl std::error::Error for Error {}
