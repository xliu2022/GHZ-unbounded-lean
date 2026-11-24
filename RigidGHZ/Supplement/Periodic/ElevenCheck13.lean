module

public import RigidGHZ.Supplement.Periodic.ElevenCheck12

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_416 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
    ?_ node_413
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
    ?_ node_414
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {16, 12} Certificate (by decide)
    ?_ node_415
  apply scheme.check_enumeration_skip 30 [31, 32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 12} Certificate (by decide)
  decide

theorem node_417 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 12} Certificate (by decide)
  decide

theorem node_418 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
    ?_ node_417
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 12} Certificate (by decide)
  decide

theorem node_419 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 12} Certificate (by decide)
  decide

theorem node_420 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
    ?_ node_419
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 12} Certificate (by decide)
  decide

theorem node_421 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 12} Certificate (by decide)
  decide

theorem node_422 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 12} Certificate (by decide)
    ?_ node_421
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 12} Certificate (by decide)
  decide

theorem node_423 :
    (scheme.enumerateFrom [] {32, 25, 12}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_424 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {25, 12} Certificate (by decide)
    ?_ node_423
  decide

theorem node_425 :
    (scheme.enumerateFrom [] {32, 29, 12}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_426 :
    (scheme.enumerateFrom [30, 31, 32] {29, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 12} Certificate (by decide)
    ?_ node_425
  decide

theorem node_427 :
    (scheme.enumerateFrom [] {32, 31, 12}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_428 :
    (scheme.enumerateFrom [32] {31, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 32 [] {31, 12} Certificate (by decide)
    ?_ node_427
  decide

theorem node_429 :
    (scheme.enumerateFrom [] {32, 12}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_430 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_410
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_412
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_416
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_418
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_420
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_422
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
    ?_ node_424
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {12} Certificate (by decide)
    ?_ node_426
  apply scheme.check_enumeration_skip 30 [31, 32] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {12} Certificate (by decide)
    ?_ node_428
  apply scheme.check_enumeration_split 32 [] {12} Certificate (by decide)
    ?_ node_429
  decide

theorem node_431 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 14, 13} Certificate (by decide)
  decide

theorem node_432 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14, 13} Certificate (by decide)
  decide

theorem node_433 :
    (scheme.enumerateFrom [31, 32] {30, 14, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 14, 13} Certificate (by decide)
  decide

theorem node_434 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
    ?_ node_431
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
    ?_ node_432
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {14, 13} Certificate (by decide)
    ?_ node_433
  apply scheme.check_enumeration_skip 31 [32] {14, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {14, 13} Certificate (by decide)
  decide

theorem node_435 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 15, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 15, 13} Certificate (by decide)
  decide

theorem node_436 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
    ?_ node_435
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 13} Certificate (by decide)
  decide

theorem node_437 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 18, 13} Certificate (by decide)
  decide

theorem node_438 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
    ?_ node_437
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 13} Certificate (by decide)
  decide

theorem node_439 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 21, 20, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 21, 20, 13} Certificate (by decide)
  decide

theorem node_440 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
    ?_ node_439
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 20, 13} Certificate (by decide)
  decide

theorem node_441 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 13} Certificate (by decide)
  decide

theorem node_442 :
    (scheme.enumerateFrom [31, 32] {30, 20, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 20, 13} Certificate (by decide)
  decide

theorem node_443 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
    ?_ node_440
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
    ?_ node_441
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {20, 13} Certificate (by decide)
    ?_ node_442
  apply scheme.check_enumeration_skip 31 [32] {20, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 13} Certificate (by decide)
  decide

theorem node_444 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 21, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 21, 13} Certificate (by decide)
  decide

theorem node_445 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 21, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 21, 13} Certificate (by decide)
  decide

theorem node_446 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
    ?_ node_444
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
    ?_ node_445
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 13} Certificate (by decide)
  decide

theorem node_447 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 13} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
