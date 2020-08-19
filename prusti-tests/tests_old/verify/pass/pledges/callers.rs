#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

struct Point { x: u32, y: u32 }

#[pledge(after_unblocked(p.x) == before_expiry(*result))]
#[pledge(after_unblocked(p.y) == 0)]
fn f0(p: &mut Point) -> &mut u32 {
    p.y = 0;
    &mut p.x
}

fn f1() {
    let mut p = Point { x: 0, y: 0 };
    let px = f0(&mut p);
    *px += 1;
    assert!(p.x == 1);
}

fn main() {}
