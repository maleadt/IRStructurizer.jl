// Q3: `if a || b { body }`.  body is reached from both arms; the edge
// multiplexer emits it exactly once (no tail duplication).
func.func @q3(%a: i1, %b: i1, %arg: memref<i32>) {
  cf.cond_br %a, ^body, ^chk
^chk:
  cf.cond_br %b, ^body, ^merge
^body:
  %v = arith.constant 99 : i32
  memref.store %v, %arg[] : memref<i32>
  cf.br ^merge
^merge:
  return
}
