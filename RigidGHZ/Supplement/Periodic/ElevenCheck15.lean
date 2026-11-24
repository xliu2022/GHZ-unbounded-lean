module

public import RigidGHZ.Supplement.Periodic.ElevenCheck14

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_480 :
    (scheme.enumerateFrom [30, 31, 32] {29, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 15} Certificate (by decide)
  decide

theorem node_481 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_463
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_467
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_471
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_475
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_477
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {15} Certificate (by decide)
    ?_ node_479
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {15} Certificate (by decide)
    ?_ node_480
  apply scheme.check_enumeration_skip 30 [31, 32] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15} Certificate (by decide)
  decide

theorem node_482 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17, 16} Certificate (by decide)
  decide

theorem node_483 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 17, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 17, 16} Certificate (by decide)
  decide

theorem node_484 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 17, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 17, 16} Certificate (by decide)
  decide

theorem node_485 :
    (scheme.enumerateFrom [31, 32] {30, 17, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17, 16} Certificate (by decide)
  decide

theorem node_486 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
    ?_ node_482
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
    ?_ node_483
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
    ?_ node_484
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17, 16} Certificate (by decide)
    ?_ node_485
  apply scheme.check_enumeration_skip 31 [32] {17, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16} Certificate (by decide)
  decide

theorem node_487 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18, 16} Certificate (by decide)
  decide

theorem node_488 :
    (scheme.enumerateFrom [30, 31, 32] {29, 18, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 18, 16} Certificate (by decide)
  decide

theorem node_489 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
    ?_ node_487
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {18, 16} Certificate (by decide)
    ?_ node_488
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 16} Certificate (by decide)
  decide

theorem node_490 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 19, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 19, 16} Certificate (by decide)
  decide

theorem node_491 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 19, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 19, 16} Certificate (by decide)
  decide

theorem node_492 :
    (scheme.enumerateFrom [31, 32] {30, 19, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19, 16} Certificate (by decide)
  decide

theorem node_493 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
    ?_ node_490
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
    ?_ node_491
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19, 16} Certificate (by decide)
    ?_ node_492
  apply scheme.check_enumeration_skip 31 [32] {19, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16} Certificate (by decide)
  decide

theorem node_494 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 21, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 21, 16} Certificate (by decide)
  decide

theorem node_495 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
    ?_ node_494
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 16} Certificate (by decide)
  decide

theorem node_496 :
    (scheme.enumerateFrom [30, 31, 32] {29, 23, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 23, 16} Certificate (by decide)
  decide

theorem node_497 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {23, 16} Certificate (by decide)
    ?_ node_496
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 16} Certificate (by decide)
  decide

theorem node_498 :
    (scheme.enumerateFrom [30, 31, 32] {29, 24, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 24, 16} Certificate (by decide)
  decide

theorem node_499 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {24, 16} Certificate (by decide)
    ?_ node_498
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 16} Certificate (by decide)
  decide

theorem node_500 :
    (scheme.enumerateFrom [30, 31, 32] {29, 27, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 27, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 27, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 27, 16} Certificate (by decide)
  decide

theorem node_501 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 16} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {27, 16} Certificate (by decide)
    ?_ node_500
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 16} Certificate (by decide)
  decide

theorem node_502 :
    (scheme.enumerateFrom [30, 31, 32] {29, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 16} Certificate (by decide)
  decide

theorem node_503 :
    (scheme.enumerateFrom [31, 32] {30, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 16} Certificate (by decide)
  decide

theorem node_504 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_486
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_489
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_493
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_495
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_497
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_499
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {16} Certificate (by decide)
    ?_ node_501
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {16} Certificate (by decide)
    ?_ node_502
  apply scheme.check_enumeration_split 30 [31, 32] {16} Certificate (by decide)
    ?_ node_503
  apply scheme.check_enumeration_skip 31 [32] {16} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16} Certificate (by decide)
  decide

theorem node_505 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 18, 17} Certificate (by decide)
  decide

theorem node_506 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 18, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 18, 17} Certificate (by decide)
  decide

theorem node_507 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 18, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 18, 17} Certificate (by decide)
  decide

theorem node_508 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
    ?_ node_505
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
    ?_ node_506
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {18, 17} Certificate (by decide)
    ?_ node_507
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17} Certificate (by decide)
  decide

theorem node_509 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 17} Certificate (by decide)
  decide

theorem node_510 :
    (scheme.enumerateFrom [31, 32] {30, 20, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 20, 17} Certificate (by decide)
  decide

theorem node_511 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
    ?_ node_509
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {20, 17} Certificate (by decide)
    ?_ node_510
  apply scheme.check_enumeration_skip 31 [32] {20, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 17} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
