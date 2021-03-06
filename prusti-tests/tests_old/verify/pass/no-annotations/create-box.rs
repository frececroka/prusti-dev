//! Currently unsupported because `Box` and `Option` use a type parameter

#![feature(nll)]
#![feature(box_patterns)]
#![feature(box_syntax)]

use prusti_contracts::*;

fn use_box(v: i32) -> Box<i32> {
    let x = Box::new(v);
    let y = *x;
    assert!(v == y);
    let z = Box::new(y);
    assert!(v == *z);
    box *z
}

fn main() {}
