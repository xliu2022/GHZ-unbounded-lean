module

public import RigidGHZ.Supplement.Periodic.ElevenCheck15

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_512 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 23, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 23, 17} Certificate (by decide)
  decide

theorem node_513 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {23, 17} Certificate (by decide)
    ?_ node_512
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 17} Certificate (by decide)
  decide

theorem node_514 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 24, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 24, 17} Certificate (by decide)
  decide

theorem node_515 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 24, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 24, 17} Certificate (by decide)
    ?_ node_514
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 24, 17} Certificate (by decide)
  decide

theorem node_516 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 24, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 24, 17} Certificate (by decide)
  decide

theorem node_517 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {24, 17} Certificate (by decide)
    ?_ node_515
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {24, 17} Certificate (by decide)
    ?_ node_516
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 17} Certificate (by decide)
  decide

theorem node_518 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 17} Certificate (by decide)
  decide

theorem node_519 :
    (scheme.enumerateFrom [31, 32] {30, 25, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 17} Certificate (by decide)
  decide

theorem node_520 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 17} Certificate (by decide)
    ?_ node_518
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 17} Certificate (by decide)
    ?_ node_519
  apply scheme.check_enumeration_skip 31 [32] {25, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17} Certificate (by decide)
  decide

theorem node_521 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 26, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 26, 17} Certificate (by decide)
  decide

theorem node_522 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {26, 17} Certificate (by decide)
    ?_ node_521
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 17} Certificate (by decide)
  decide

theorem node_523 :
    (scheme.enumerateFrom [31, 32] {30, 28, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 28, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 28, 17} Certificate (by decide)
  decide

theorem node_524 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 17} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {28, 17} Certificate (by decide)
    ?_ node_523
  apply scheme.check_enumeration_skip 31 [32] {28, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 17} Certificate (by decide)
  decide

theorem node_525 :
    (scheme.enumerateFrom [31, 32] {30, 17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17} Certificate (by decide)
  decide

theorem node_526 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_508
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_511
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_513
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_517
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_520
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_522
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {17} Certificate (by decide)
    ?_ node_524
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17} Certificate (by decide)
    ?_ node_525
  apply scheme.check_enumeration_skip 31 [32] {17} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17} Certificate (by decide)
  decide

theorem node_527 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 19, 18} Certificate (by decide)
  decide

theorem node_528 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 18} Certificate (by decide)
  decide

theorem node_529 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 19, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 19, 18} Certificate (by decide)
  decide

theorem node_530 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
    ?_ node_527
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
    ?_ node_528
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {19, 18} Certificate (by decide)
    ?_ node_529
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18} Certificate (by decide)
  decide

theorem node_531 :
    (scheme.enumerateFrom [30, 31, 32] {29, 20, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 20, 18} Certificate (by decide)
  decide

theorem node_532 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {20, 18} Certificate (by decide)
    ?_ node_531
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 18} Certificate (by decide)
  decide

theorem node_533 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 18} Certificate (by decide)
  decide

theorem node_534 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 18} Certificate (by decide)
    ?_ node_533
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 18} Certificate (by decide)
  decide

theorem node_535 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 18} Certificate (by decide)
  decide

theorem node_536 :
    (scheme.enumerateFrom [30, 31, 32] {29, 28, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 28, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 28, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 28, 18} Certificate (by decide)
  decide

theorem node_537 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 29 [30, 31, 32] {28, 18} Certificate (by decide)
    ?_ node_536
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 18} Certificate (by decide)
  decide

theorem node_538 :
    (scheme.enumerateFrom [30, 31, 32] {29, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 18} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 18} Certificate (by decide)
  decide

theorem node_539 :
    (scheme.enumerateFrom [32] {31, 18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 18} Certificate (by decide)
  decide

theorem node_540 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
    ?_ node_530
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
    ?_ node_532
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
    ?_ node_534
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
    ?_ node_535
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {18} Certificate (by decide)
    ?_ node_537
  apply scheme.check_enumeration_split 29 [30, 31, 32] {18} Certificate (by decide)
    ?_ node_538
  apply scheme.check_enumeration_skip 30 [31, 32] {18} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {18} Certificate (by decide)
    ?_ node_539
  apply scheme.check_enumeration_skip 32 [] {18} Certificate (by decide)
  decide

theorem node_541 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 19} Certificate (by decide)
  decide

theorem node_542 :
    (scheme.enumerateFrom [31, 32] {30, 20, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 20, 19} Certificate (by decide)
  decide

theorem node_543 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
    ?_ node_541
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {20, 19} Certificate (by decide)
    ?_ node_542
  apply scheme.check_enumeration_skip 31 [32] {20, 19} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 19} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
