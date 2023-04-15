use serde::Serialize;
use serde_json::Serializer;
use serde_json_fmt::JsonOptions;

#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
struct Structure {
    pub name: String,
    pub size: i32,
    pub on: bool,
}

#[test]
fn test_json_formatter_owned_is_formatter() {
    // Test that JsonFormatterOwned is usable as a Formatter implementation
    // outside the crate despite the implementation involving private stuff.
    let value = Structure {
        name: "foo".into(),
        size: 42,
        on: false,
    };
    let formatter = JsonOptions::pretty().build();
    let mut vec = Vec::with_capacity(128);
    let mut ser = Serializer::with_formatter(&mut vec, formatter);
    value.serialize(&mut ser).unwrap();
    let s = String::from_utf8(vec).unwrap();
    assert_eq!(
        s,
        concat!(
            "{\n",
            "  \"name\": \"foo\",\n",
            "  \"size\": 42,\n",
            "  \"on\": false\n",
            "}"
        )
    );
}

#[test]
fn test_json_format_is_formatter() {
    // Test that JsonFormatter is usable as a Formatter implementation outside
    // the crate despite the implementation involving private stuff.
    let value = Structure {
        name: "foo".into(),
        size: 42,
        on: false,
    };
    let builder = JsonOptions::pretty();
    let formatter = builder.as_formatter();
    let mut vec = Vec::with_capacity(128);
    let mut ser = Serializer::with_formatter(&mut vec, formatter);
    value.serialize(&mut ser).unwrap();
    let s = String::from_utf8(vec).unwrap();
    assert_eq!(
        s,
        concat!(
            "{\n",
            "  \"name\": \"foo\",\n",
            "  \"size\": 42,\n",
            "  \"on\": false\n",
            "}"
        )
    );
}
