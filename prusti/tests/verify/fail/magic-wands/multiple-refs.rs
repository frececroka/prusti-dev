#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

struct Point { x: u32, y: u32 }

#[pledge(after_unblocked(after_unblocked(p.x)) == before_expiry(*result))]
fn f00(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(before_expiry(*result)) == before_expiry(*result))]
fn f01(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x) == before_expiry(after_unblocked(p.x)))]
fn f02(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x) == before_expiry(before_expiry(*result)))]
fn f03(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(*result) == before_expiry(*result))]
fn f10(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x) == before_expiry(p.x))]
fn f11(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x + q.x) == before_expiry(*result))]
fn f20<'p, 'q>(p: &'p mut Point, q: &'q mut Point) -> &'p mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x) == before_expiry(*result.0 + *result.1))]
fn f21<'p, 'q>(p: &'p mut Point, q: &'q mut Point) -> (&'p mut u32, &'q mut u32) {
    (&mut p.x, &mut q.x)
}

#[pledge(after_unblocked(0) == before_expiry(*result))]
fn f30(p: &mut Point) -> &mut u32 {
    &mut p.x
}

#[pledge(after_unblocked(p.x) == before_expiry(0))]
fn f31(p: &mut Point) -> &mut u32 {
    &mut p.x
}

fn main() {}
