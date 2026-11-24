module

public import RigidGHZ.Supplement.Periodic.ElevenCheck13

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_448 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 24, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 24, 13} Certificate (by decide)
  decide

theorem node_449 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {24, 13} Certificate (by decide)
    ?_ node_448
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 13} Certificate (by decide)
  decide

theorem node_450 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 13} Certificate (by decide)
  decide

theorem node_451 :
    (scheme.enumerateFrom [31, 32] {30, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 13} Certificate (by decide)
  decide

theorem node_452 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_434
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_436
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_438
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_443
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_446
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_447
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_449
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {13} Certificate (by decide)
    ?_ node_450
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {13} Certificate (by decide)
    ?_ node_451
  apply scheme.check_enumeration_skip 31 [32] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13} Certificate (by decide)
  decide

theorem node_453 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 14} Certificate (by decide)
  decide

theorem node_454 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14} Certificate (by decide)
  decide

theorem node_455 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 14} Certificate (by decide)
  decide

theorem node_456 :
    (scheme.enumerateFrom [] {32, 30, 14}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_457 :
    (scheme.enumerateFrom [31, 32] {30, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 14} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {30, 14} Certificate (by decide)
    ?_ node_456
  decide

theorem node_458 :
    (scheme.enumerateFrom [] {32, 14}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_459 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
    ?_ node_453
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14} Certificate (by decide)
    ?_ node_454
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {14} Certificate (by decide)
    ?_ node_455
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {14} Certificate (by decide)
    ?_ node_457
  apply scheme.check_enumeration_skip 31 [32] {14} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {14} Certificate (by decide)
    ?_ node_458
  decide

theorem node_460 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 15} Certificate (by decide)
  decide

theorem node_461 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 15} Certificate (by decide)
  decide

theorem node_462 :
    (scheme.enumerateFrom [30, 31, 32] {29, 16, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 16, 15} Certificate (by decide)
  decide

theorem node_463 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
    ?_ node_460
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
    ?_ node_461
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {16, 15} Certificate (by decide)
    ?_ node_462
  apply scheme.check_enumeration_skip 30 [31, 32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 15} Certificate (by decide)
  decide

theorem node_464 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 17, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 17, 15} Certificate (by decide)
  decide

theorem node_465 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 17, 15} Certificate (by decide)
    ?_ node_464
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 15} Certificate (by decide)
  decide

theorem node_466 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 17, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 17, 15} Certificate (by decide)
  decide

theorem node_467 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
    ?_ node_465
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
    ?_ node_466
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 15} Certificate (by decide)
  decide

theorem node_468 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 19, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 19, 15} Certificate (by decide)
  decide

theorem node_469 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 19, 15} Certificate (by decide)
    ?_ node_468
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 15} Certificate (by decide)
  decide

theorem node_470 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 19, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 19, 15} Certificate (by decide)
  decide

theorem node_471 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
    ?_ node_469
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
    ?_ node_470
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 15} Certificate (by decide)
  decide

theorem node_472 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 22, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 22, 15} Certificate (by decide)
  decide

theorem node_473 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 22, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 22, 15} Certificate (by decide)
    ?_ node_472
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 22, 15} Certificate (by decide)
  decide

theorem node_474 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 15} Certificate (by decide)
  decide

theorem node_475 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {22, 15} Certificate (by decide)
    ?_ node_473
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 15} Certificate (by decide)
    ?_ node_474
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 15} Certificate (by decide)
  decide

theorem node_476 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 15} Certificate (by decide)
  decide

theorem node_477 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 15} Certificate (by decide)
    ?_ node_476
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 15} Certificate (by decide)
  decide

theorem node_478 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 15} Certificate (by decide)
  decide

theorem node_479 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 15} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 15} Certificate (by decide)
    ?_ node_478
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 15} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
