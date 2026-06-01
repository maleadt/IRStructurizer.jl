module {
  func.func @q2(%arg0: i1, %arg1: i1) -> i32 {
    %c1_i32 = arith.constant 1 : i32
    %0 = ub.poison : i32
    %c0_i32 = arith.constant 0 : i32
    %c100_i32 = arith.constant 100 : i32
    %c200_i32 = arith.constant 200 : i32
    %c999_i32 = arith.constant 999 : i32
    %1:3 = scf.if %arg0 -> (i32, i32, i32) {
      scf.yield %c100_i32, %0, %c0_i32 : i32, i32, i32
    } else {
      %4:3 = scf.if %arg1 -> (i32, i32, i32) {
        scf.yield %c200_i32, %0, %c0_i32 : i32, i32, i32
      } else {
        scf.yield %0, %c999_i32, %c1_i32 : i32, i32, i32
      }
      scf.yield %4#0, %4#1, %4#2 : i32, i32, i32
    }
    %2 = arith.index_castui %1#2 : i32 to index
    %3 = scf.index_switch %2 -> i32 
    case 0 {
      scf.yield %1#0 : i32
    }
    default {
      scf.yield %1#1 : i32
    }
    return %3 : i32
  }
}

