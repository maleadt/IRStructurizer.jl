module {
  func.func @q1(%arg0: i1) -> i32 {
    %c0_i32 = arith.constant 0 : i32
    %c10_i32 = arith.constant 10 : i32
    %c20_i32 = arith.constant 20 : i32
    %0 = scf.if %arg0 -> (i32) {
      scf.yield %c10_i32 : i32
    } else {
      scf.yield %c20_i32 : i32
    }
    return %0 : i32
  }
}

