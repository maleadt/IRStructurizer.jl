// Q2: E->{T,F}, T->M, F->{M,R}, R:return, M->X.  ipdom(E)=virtual exit, yet the
// continuation is unambiguously M (no block-index tie-break needed).
func.func @q2(%c: i1, %c2: i1) -> i32 {
  %m_t = arith.constant 100 : i32
  %m_f = arith.constant 200 : i32
  %r   = arith.constant 999 : i32
  cf.cond_br %c, ^T, ^F
^T:
  cf.br ^M(%m_t : i32)
^F:
  cf.cond_br %c2, ^M(%m_f : i32), ^R
^R:
  return %r : i32
^M(%v: i32):
  cf.br ^X
^X:
  return %v : i32
}
