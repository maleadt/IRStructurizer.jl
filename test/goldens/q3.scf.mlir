module {
  func.func @q3(%arg0: i1, %arg1: i1, %arg2: memref<i32>) {
    %c1_i32 = arith.constant 1 : i32
    %c0_i32 = arith.constant 0 : i32
    %0 = scf.if %arg0 -> (i32) {
      scf.yield %c0_i32 : i32
    } else {
      %2 = scf.if %arg1 -> (i32) {
        scf.yield %c0_i32 : i32
      } else {
        scf.yield %c1_i32 : i32
      }
      scf.yield %2 : i32
    }
    %1 = arith.index_castui %0 : i32 to index
    scf.index_switch %1 
    case 0 {
      %c99_i32 = arith.constant 99 : i32
      memref.store %c99_i32, %arg2[] : memref<i32>
      scf.yield
    }
    default {
    }
    return
  }
}

