// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

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
