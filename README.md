[![Project Status: Active – The project has reached a stable, usable state and is being actively developed.](https://www.repostatus.org/badges/latest/active.svg)](https://www.repostatus.org/#active)
[![CI Status](https://github.com/jwodder/serde-json-fmt/actions/workflows/test.yml/badge.svg)](https://github.com/jwodder/serde-json-fmt/actions/workflows/test.yml)
[![codecov.io](https://codecov.io/gh/jwodder/serde-json-fmt/branch/master/graph/badge.svg)](https://codecov.io/gh/jwodder/serde-json-fmt)
[![Minimum Supported Rust Version](https://img.shields.io/badge/MSRV-1.65-orange)](https://www.rust-lang.org)
[![MIT License](https://img.shields.io/github/license/jwodder/serde-json-fmt.svg)](https://opensource.org/licenses/MIT)

[GitHub](https://github.com/jwodder/serde-json-fmt) | [crates.io](https://crates.io/crates/serde-json-fmt) | [Documentation](https://docs.rs/serde-json-fmt) | [Issues](https://github.com/jwodder/serde-json-fmt/issues) | [Changelog](https://github.com/jwodder/serde-json-fmt/blob/master/CHANGELOG.md)

The `serde-json-fmt` crate lets you create custom
[`serde_json`](https://crates.io/crates/serde_json) formatters with the
indentation, separators, and ASCII requirements of your choice.

`serde_json` itself only directly provides the ability to produce JSON in
either "compact" form or "pretty" form, with the only customizable aspect being
the string used for pretty indentation.  `serde-json-fmt` complements
`serde_json` to let you also customize the whitespace around commas & colons
and whether to escape non-ASCII characters.

Examples
========

Say you want to serialize a value in one-line "compact" form, but you want a
space after each colon & comma, something that `serde_json`'s compact form
doesn't do.  `serde-json-fmt` lets you do that:

```rust
use serde_json::json;
use serde_json_fmt::JsonFormat;

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
```

Say you want to format a value in multiline "pretty" form, but using four-space
indents and with all non-ASCII characters encoded as `\uXXXX` escape sequences.
`serde-json-fmt` lets you do that:

```rust
use serde_json::json;
use serde_json_fmt::JsonFormat;

let value = json!({
    "emojis": {
        "goat":"🐐",
        "pineapple": "🍍",
        "smile": "😀",
    },
    "greek": {
        "α": "alpha",
        "β": "beta",
        "γ": "gamma",
    }
});

let s = JsonFormat::pretty()
    .indent_width(Some(4))
    .ascii(true)
    .format_to_string(&value)
    .unwrap();

assert_eq!(s, r#"{
    "emojis": {
        "goat": "\ud83d\udc10",
        "pineapple": "\ud83c\udf4d",
        "smile": "\ud83d\ude00"
    },
    "greek": {
        "\u03b1": "alpha",
        "\u03b2": "beta",
        "\u03b3": "gamma"
    }
}"#);
```
