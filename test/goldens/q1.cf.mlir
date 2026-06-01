// Q1: E->{T,F}, F->T, T->X.  T has two predecessors ⇒ T is the continuation,
// not part of the then-region (edge-domination, not block-domination).
func.func @q1(%c: i1) -> i32 {
  %t = arith.constant 10 : i32
  %f = arith.constant 20 : i32
  cf.cond_br %c, ^T(%t : i32), ^F
^F:
  cf.br ^T(%f : i32)
^T(%v: i32):
  cf.br ^X
^X:
  return %v : i32
}
