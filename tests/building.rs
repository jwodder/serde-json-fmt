use indoc::indoc;
use serde::Serialize;
use serde_json::{json, Serializer};
use serde_json_fmt::JsonFormat;

#[test]
fn test_json_formatter_is_formatter() {
    // Test that JsonFormatter is usable as a Formatter implementation outside
    // the crate despite the implementation involving private stuff.
    let value = json!({
        "name": "foo",
        "on": false,
        "size": 42
    });
    let formatter = JsonFormat::pretty().build();
    let mut vec = Vec::with_capacity(128);
    let mut ser = Serializer::with_formatter(&mut vec, formatter);
    value.serialize(&mut ser).unwrap();
    let s = String::from_utf8(vec).unwrap();
    assert_eq!(
        s,
        indoc! {r#"{
          "name": "foo",
          "on": false,
          "size": 42
        }"#}
    );
}

#[test]
fn test_json_frmtr_is_formatter() {
    // Test that JsonFrmtr is usable as a Formatter implementation outside the
    // crate despite the implementation involving private stuff.
    let value = json!({
        "name": "foo",
        "on": false,
        "size": 42
    });
    let builder = JsonFormat::pretty();
    let formatter = builder.as_formatter();
    let mut vec = Vec::with_capacity(128);
    let mut ser = Serializer::with_formatter(&mut vec, formatter);
    value.serialize(&mut ser).unwrap();
    let s = String::from_utf8(vec).unwrap();
    assert_eq!(
        s,
        indoc! {r#"{
          "name": "foo",
          "on": false,
          "size": 42
        }"#}
    );
}
