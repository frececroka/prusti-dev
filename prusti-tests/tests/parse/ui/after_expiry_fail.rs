// compile-flags: -Zprint-desugared-specs -Zprint-typeckd-specs -Zskip-verify -Zhide-uuids
// normalize-stdout-test: "[a-z0-9]{32}" -> "$(NUM_UUID)"
// normalize-stdout-test: "[a-z0-9]{8}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{4}-[a-z0-9]{12}" -> "$(UUID)"

use prusti_contracts::*;

#[after_expiry_if(a)]
fn test1() {}

#[after_expiry_if(a => a)]
fn test2() {}

#[after_expiry(a, a)]
fn test3() {}

#[after_expiry(a => a, a)]
fn test4() {}

fn main() {}
