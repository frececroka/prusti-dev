#![feature(register_tool)]
#![register_tool(prusti)]

use prusti_contracts::*;

struct Point { x: u32, y: u32 }

#[pledge(after_unblocked(p.x) == before_expiry(*result.0))]
#[pledge(after_unblocked(q.x) == before_expiry(*result.1))]
#[pledge(after_unblocked(p.y) == after_unblocked(q.y))]
fn f1<'p, 'q>(p: &'p mut Point, q: &'q mut Point) -> (&'p mut u32, &'q mut u32) {
    p.y = q.y;
    (&mut p.x, &mut q.x)
}

fn f2<'a: 'b, 'b>(p: &'a mut Point, q: &'b mut Point) -> (&'a mut u32, &'b mut u32) {
    (&mut p.x, &mut q.x)
}

fn f3<'a: 'b, 'b>(p: &'a mut Point) -> (&'a mut u32, &mut u32) {
    (&mut p.x, &mut p.y)
}

fn f4<'a: 'd, 'b: 'd + 'e, 'c: 'f, 'd, 'e, 'f>(
    a: &'a mut Point,
    b: &'b mut Point,
    c: &'c mut Point
) -> (&'d mut u32, &'e mut u32, &'f mut u32) {
    (&mut a.x, &mut b.x, &mut c.x)
}

fn main() {}
