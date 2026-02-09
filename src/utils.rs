// Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

/// parse a string containing only '0' and '1' into a vector of bytes
pub fn parse_binary_str(s: &str) -> (Vec<u8>, usize) {
    let mut ret = Vec::new();
    let mut r: u8 = 0;
    let mut i: usize = 1;
    for c in s.chars().rev() {
        if c == '1' {
            r |= i as u8;
        }
        i *= 2;
        if i == 256 {
            i = 1;
            ret.push(r);
            r = 0;
        }
    }
    if i > 1 {
        ret.push(r);
    }
    (ret, s.len())
}

fn byte_to_string(mut b: u8, len: usize) -> String {
    let len = if len == 0 { 8 } else { len };
    let mut chars = Vec::with_capacity(len);
    while b != 0 {
        if b & 1 == 1 {
            chars.push('1');
        } else {
            chars.push('0');
        }
        b >>= 1;
    }
    while chars.len() < len {
        chars.push('0');
    }
    chars.reverse();
    chars.into_iter().collect()
}

/// assume len >= the necessary number of bits to encode `bytes`
pub fn binary_to_string(bytes: &[u8], len: usize) -> String {
    if !bytes.is_empty() {
        let mut buf = byte_to_string(bytes[bytes.len() - 1], len % 8);
        let mut strs = bytes[..bytes.len() - 1]
            .iter()
            .map(|b| byte_to_string(*b, 8))
            .collect::<Vec<_>>();
        strs.reverse();
        for s in strs {
            buf.push_str(&s);
        }
        buf
    } else {
        String::new()
    }
}

fn hex_char_to_num(c: char) -> u8 {
    c.to_digit(16).unwrap() as u8
}

/// parse a string containing only '0-9a-zA-Z' into a vector of bytes
pub fn parse_hexadecimal_str(s: &str) -> (Vec<u8>, usize) {
    let mut ret = Vec::new();
    let mut r: u8 = 0;
    let mut shift = 0;
    for c in s.chars().rev() {
        r |= hex_char_to_num(c) << shift;
        shift += 4;
        if shift == 8 {
            ret.push(r);
            shift = 0;
            r = 0;
        }
    }
    if shift > 0 {
        ret.push(r)
    }
    (ret, s.len())
}

/// assume len >= the necessary number of hex codes to encode `bytes`
pub fn hex_to_string(bytes: &[u8], len: usize) -> String {
    if !bytes.is_empty() {
        let mut hex = bytes[0..bytes.len() - 1]
            .iter()
            .map(|h| format!("{:02x}", h))
            .collect::<Vec<_>>();
        hex.push(if len.is_multiple_of(2) {
            format!("{:02x}", bytes[bytes.len() - 1])
        } else {
            format!("{:x}", bytes[bytes.len() - 1])
        });
        hex.reverse();
        hex.join("")
    } else {
        String::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lazy_static::lazy_static;
    use std::collections::HashMap;

    lazy_static! {
        static ref BINARY_TESTS: HashMap<&'static str, (Vec<u8>, usize)> = HashMap::from([
            ("0", (vec![0], 1)),
            ("10", (vec![2], 2)),
            ("0100", (vec![4], 4)),
            ("0000011", (vec![3], 7)),
            ("00000011", (vec![3], 8)),
            ("1000000001", (vec![1, 2], 10)),
        ]);
    }

    #[test]
    fn test_binary_str() {
        for (s, (v, l)) in BINARY_TESTS.iter() {
            assert_eq!(parse_binary_str(s), (v.clone(), *l));
            assert_eq!(&binary_to_string(v, *l), s);
        }
    }

    lazy_static! {
        static ref HEX_TESTS: HashMap<&'static str, (Vec<u8>, usize)> = HashMap::from([
            ("a", (vec![0xa], 1)),
            ("A", (vec![0xa], 1)),
            ("0B", (vec![0xb], 2)),
            ("aB", (vec![0xab], 2)),
            ("deadbeef", (vec![0xef, 0xbe, 0xad, 0xde], 8)),
            ("abc", (vec![0xbc, 0xa], 3))
        ]);
    }

    #[test]
    fn test_hexadecimal_str() {
        for (s, (v, l)) in HEX_TESTS.iter() {
            assert_eq!(parse_hexadecimal_str(s), (v.clone(), *l));
            assert_eq!(hex_to_string(v, *l), s.to_lowercase());
        }
    }
}
