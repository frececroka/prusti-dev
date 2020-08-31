#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

struct Point { x: u32, y: u32 }

fn f0(p: &mut Point) -> &mut u32 {
    p.y = 0;
    &mut p.x
}

fn f0_caller() {
    let mut p = Point { x: 0, y: 0 };
    let px = f0(&mut p);
    *px += 1;
}

#[pledge(after_unblocked(p.x) == before_expiry(*result))]
#[pledge(after_unblocked(p.y) == 0)]
#[ensures(*result == old(p.x))]
fn f1(p: &mut Point) -> &mut u32 {
    p.y = 0;
    &mut p.x
}

fn f1_caller() {
    let mut p = Point { x: 0, y: 0 };
    let px = f1(&mut p);
    *px += 1;
    assert!(p.x == 1);
}

fn f2(p: &mut Point) -> (&mut u32, &mut u32) {
    (&mut p.x, &mut p.y)
}

fn f2_caller() {
    let mut p = Point { x: 0, y: 0 };
    let (px, py) = f2(&mut p);
    *px += 1;
    *py += 2;
}

fn main() {}
