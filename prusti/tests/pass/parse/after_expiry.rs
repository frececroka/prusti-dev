// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

#[after_expiry_if(result => a, a)]
fn test1(a: bool) {}

#[after_expiry_if(a, a)]
fn test2(a: bool) {}

#[pledge(a)]
fn test3(a: bool) {}

#[pledge(
    result == match x {
        1 => 1,
        2 => 2,
        _ => 0,
    }
)]
fn test5(x: u32) -> u32 {
    1
}

fn main() {}
