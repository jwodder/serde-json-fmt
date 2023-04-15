use serde::Serialize;
use serde_json::ser::Formatter;
use serde_json::Serializer;
use smartstring::alias::CompactString;
use std::fmt;
use std::io::{self, Write};

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
pub struct JsonOptions {
    indent: Option<CompactString>,
    comma: CompactString,
    colon: CompactString,
    ascii: bool,
}

impl JsonOptions {
    // Uses serde-json's default/"compact" formatting
    // Note that this format omits spaces from the comma & colon separators
    pub fn new() -> Self {
        JsonOptions {
            indent: None,
            comma: ",".into(),
            colon: ":".into(),
            ascii: false,
        }
    }

    // Uses serde-json's "pretty" formatting
    pub fn pretty() -> Self {
        JsonOptions {
            indent: Some("  ".into()),
            comma: ",".into(),
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
        self.indent(n.map(|i| CompactString::from(" ").repeat(i)))
            .unwrap()
    }

    pub fn build(self) -> JsonFormatterOwned {
        JsonFormatterOwned::new(self)
    }

    pub fn as_formatter(&self) -> JsonFormatter<'_> {
        JsonFormatter::new(internal::JsonOptionsRef {
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

impl Default for JsonOptions {
    fn default() -> Self {
        JsonOptions::new()
    }
}

mod internal {
    use super::*;

    pub trait OptionsData {
        fn indent(&self) -> Option<&[u8]>;
        fn comma(&self) -> &[u8];
        fn colon(&self) -> &[u8];
        fn ascii(&self) -> bool;
    }

    impl OptionsData for JsonOptions {
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
    pub struct JsonOptionsRef<'a> {
        pub indent: Option<&'a [u8]>,
        pub comma: &'a [u8],
        pub colon: &'a [u8],
        pub ascii: bool,
    }

    impl<'a> OptionsData for JsonOptionsRef<'a> {
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
}

pub type JsonFormatterOwned = internal::JsonFormatterBase<JsonOptions>;
pub type JsonFormatter<'a> = internal::JsonFormatterBase<internal::JsonOptionsRef<'a>>;

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

#[cfg(test)]
mod tests {
    use super::*;
    //use serde::Serialize;
    use rstest::rstest;

    #[rstest]
    #[case("?", Ok("?".into()))]
    #[case(" ?", Ok(" ?".into()))]
    #[case("? ", Ok("? ".into()))]
    #[case("  ? ", Ok("  ? ".into()))]
    #[case(" \t?\r\n", Ok(" \t?\r\n".into()))]
    #[case("", Err(Error::MissingSeparator('?')))]
    #[case(" ", Err(Error::MissingSeparator('?')))]
    #[case("??", Err(Error::MultipleSeparators('?')))]
    #[case("? ?", Err(Error::MultipleSeparators('?')))]
    #[case("\x0C", Err(Error::InvalidCharacter('\x0C')))]
    #[case("\x0B", Err(Error::InvalidCharacter('\x0B')))]
    #[case("\u{A0}", Err(Error::InvalidCharacter('\u{A0}')))]
    #[case("\u{85}", Err(Error::InvalidCharacter('\u{85}')))]
    #[case("\u{1680}", Err(Error::InvalidCharacter('\u{1680}')))]
    #[case("\u{180E}", Err(Error::InvalidCharacter('\u{180E}')))]
    #[case("\u{2000}", Err(Error::InvalidCharacter('\u{2000}')))]
    #[case("\u{2001}", Err(Error::InvalidCharacter('\u{2001}')))]
    #[case("\u{2002}", Err(Error::InvalidCharacter('\u{2002}')))]
    #[case("\u{2003}", Err(Error::InvalidCharacter('\u{2003}')))]
    #[case("\u{2004}", Err(Error::InvalidCharacter('\u{2004}')))]
    #[case("\u{2005}", Err(Error::InvalidCharacter('\u{2005}')))]
    #[case("\u{2006}", Err(Error::InvalidCharacter('\u{2006}')))]
    #[case("\u{2007}", Err(Error::InvalidCharacter('\u{2007}')))]
    #[case("\u{2008}", Err(Error::InvalidCharacter('\u{2008}')))]
    #[case("\u{2009}", Err(Error::InvalidCharacter('\u{2009}')))]
    #[case("\u{200A}", Err(Error::InvalidCharacter('\u{200A}')))]
    #[case("\u{200B}", Err(Error::InvalidCharacter('\u{200B}')))]
    #[case("\u{200C}", Err(Error::InvalidCharacter('\u{200C}')))]
    #[case("\u{200D}", Err(Error::InvalidCharacter('\u{200D}')))]
    #[case("\u{2028}", Err(Error::InvalidCharacter('\u{2028}')))]
    #[case("\u{2029}", Err(Error::InvalidCharacter('\u{2029}')))]
    #[case("\u{202F}", Err(Error::InvalidCharacter('\u{202F}')))]
    #[case("\u{205F}", Err(Error::InvalidCharacter('\u{205F}')))]
    #[case("\u{2060}", Err(Error::InvalidCharacter('\u{2060}')))]
    #[case("\u{3000}", Err(Error::InvalidCharacter('\u{3000}')))]
    #[case("\u{FEFF}", Err(Error::InvalidCharacter('\u{FEFF}')))]
    #[case("\x0C?", Err(Error::InvalidCharacter('\x0C')))]
    #[case("?\x0C", Err(Error::InvalidCharacter('\x0C')))]
    #[case("?\x0C?", Err(Error::InvalidCharacter('\x0C')))]
    #[case("??\x0C", Err(Error::MultipleSeparators('?')))]
    #[case(".", Err(Error::InvalidCharacter('.')))]
    #[case(".?", Err(Error::InvalidCharacter('.')))]
    #[case("?.", Err(Error::InvalidCharacter('.')))]
    #[case("?.?", Err(Error::InvalidCharacter('.')))]
    #[case("??.", Err(Error::MultipleSeparators('?')))]
    #[case("☃", Err(Error::InvalidCharacter('☃')))]
    #[case("☃?", Err(Error::InvalidCharacter('☃')))]
    #[case("?☃", Err(Error::InvalidCharacter('☃')))]
    #[case("?☃?", Err(Error::InvalidCharacter('☃')))]
    #[case("??☃", Err(Error::MultipleSeparators('?')))]
    fn test_validate_string_sep(#[case] s: &str, #[case] r: Result<CompactString, Error>) {
        assert_eq!(validate_string(s, Some('?')), r);
    }

    #[rstest]
    #[case("", Ok("".into()))]
    #[case(" ", Ok(" ".into()))]
    #[case("    ", Ok("    ".into()))]
    #[case(" \t\r\n", Ok(" \t\r\n".into()))]
    #[case("?", Err(Error::InvalidCharacter('?')))]
    #[case(" ?", Err(Error::InvalidCharacter('?')))]
    #[case("? ", Err(Error::InvalidCharacter('?')))]
    #[case("  ? ", Err(Error::InvalidCharacter('?')))]
    #[case("??", Err(Error::InvalidCharacter('?')))]
    #[case("\x0C", Err(Error::InvalidCharacter('\x0C')))]
    #[case("\x0B", Err(Error::InvalidCharacter('\x0B')))]
    #[case("\u{A0}", Err(Error::InvalidCharacter('\u{A0}')))]
    #[case("\u{85}", Err(Error::InvalidCharacter('\u{85}')))]
    #[case("\u{1680}", Err(Error::InvalidCharacter('\u{1680}')))]
    #[case("\u{180E}", Err(Error::InvalidCharacter('\u{180E}')))]
    #[case("\u{2000}", Err(Error::InvalidCharacter('\u{2000}')))]
    #[case("\u{2001}", Err(Error::InvalidCharacter('\u{2001}')))]
    #[case("\u{2002}", Err(Error::InvalidCharacter('\u{2002}')))]
    #[case("\u{2003}", Err(Error::InvalidCharacter('\u{2003}')))]
    #[case("\u{2004}", Err(Error::InvalidCharacter('\u{2004}')))]
    #[case("\u{2005}", Err(Error::InvalidCharacter('\u{2005}')))]
    #[case("\u{2006}", Err(Error::InvalidCharacter('\u{2006}')))]
    #[case("\u{2007}", Err(Error::InvalidCharacter('\u{2007}')))]
    #[case("\u{2008}", Err(Error::InvalidCharacter('\u{2008}')))]
    #[case("\u{2009}", Err(Error::InvalidCharacter('\u{2009}')))]
    #[case("\u{200A}", Err(Error::InvalidCharacter('\u{200A}')))]
    #[case("\u{200B}", Err(Error::InvalidCharacter('\u{200B}')))]
    #[case("\u{200C}", Err(Error::InvalidCharacter('\u{200C}')))]
    #[case("\u{200D}", Err(Error::InvalidCharacter('\u{200D}')))]
    #[case("\u{2028}", Err(Error::InvalidCharacter('\u{2028}')))]
    #[case("\u{2029}", Err(Error::InvalidCharacter('\u{2029}')))]
    #[case("\u{202F}", Err(Error::InvalidCharacter('\u{202F}')))]
    #[case("\u{205F}", Err(Error::InvalidCharacter('\u{205F}')))]
    #[case("\u{2060}", Err(Error::InvalidCharacter('\u{2060}')))]
    #[case("\u{3000}", Err(Error::InvalidCharacter('\u{3000}')))]
    #[case("\u{FEFF}", Err(Error::InvalidCharacter('\u{FEFF}')))]
    #[case("\x0C ", Err(Error::InvalidCharacter('\x0C')))]
    #[case(" \x0C", Err(Error::InvalidCharacter('\x0C')))]
    #[case(" \x0C ", Err(Error::InvalidCharacter('\x0C')))]
    #[case(".", Err(Error::InvalidCharacter('.')))]
    #[case(". ", Err(Error::InvalidCharacter('.')))]
    #[case(" .", Err(Error::InvalidCharacter('.')))]
    #[case(" . ", Err(Error::InvalidCharacter('.')))]
    #[case("☃", Err(Error::InvalidCharacter('☃')))]
    #[case("☃ ", Err(Error::InvalidCharacter('☃')))]
    #[case(" ☃", Err(Error::InvalidCharacter('☃')))]
    #[case(" ☃ ", Err(Error::InvalidCharacter('☃')))]
    fn test_validate_string_no_sep(#[case] s: &str, #[case] r: Result<CompactString, Error>) {
        assert_eq!(validate_string(s, None), r);
    }
}
