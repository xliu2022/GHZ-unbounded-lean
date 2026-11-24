module

public import RigidGHZ.Supplement.Periodic.ElevenCheck11

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_384 :
    (scheme.enumerateFrom [] {32, 29, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_385 :
    (scheme.enumerateFrom [30, 31, 32] {29, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 12, 11} Certificate (by decide)
    ?_ node_384
  decide

theorem node_386 :
    (scheme.enumerateFrom [] {32, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_387 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
    ?_ node_381
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
    ?_ node_382
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
    ?_ node_383
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {12, 11} Certificate (by decide)
    ?_ node_385
  apply scheme.check_enumeration_skip 30 [31, 32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {12, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {12, 11} Certificate (by decide)
    ?_ node_386
  decide

theorem node_388 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 13, 11} Certificate (by decide)
  decide

theorem node_389 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 13, 11} Certificate (by decide)
  decide

theorem node_390 :
    (scheme.enumerateFrom [31, 32] {30, 13, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 13, 11} Certificate (by decide)
  decide

theorem node_391 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
    ?_ node_388
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
    ?_ node_389
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {13, 11} Certificate (by decide)
    ?_ node_390
  apply scheme.check_enumeration_skip 31 [32] {13, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 11} Certificate (by decide)
  decide

theorem node_392 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17, 11} Certificate (by decide)
  decide

theorem node_393 :
    (scheme.enumerateFrom [31, 32] {30, 17, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17, 11} Certificate (by decide)
  decide

theorem node_394 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
    ?_ node_392
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17, 11} Certificate (by decide)
    ?_ node_393
  apply scheme.check_enumeration_skip 31 [32] {17, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 11} Certificate (by decide)
  decide

theorem node_395 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18, 11} Certificate (by decide)
  decide

theorem node_396 :
    (scheme.enumerateFrom [30, 31, 32] {29, 18, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 18, 11} Certificate (by decide)
  decide

theorem node_397 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
    ?_ node_395
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {18, 11} Certificate (by decide)
    ?_ node_396
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 11} Certificate (by decide)
  decide

theorem node_398 :
    (scheme.enumerateFrom [31, 32] {30, 19, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19, 11} Certificate (by decide)
  decide

theorem node_399 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19, 11} Certificate (by decide)
    ?_ node_398
  apply scheme.check_enumeration_skip 31 [32] {19, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 11} Certificate (by decide)
  decide

theorem node_400 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 11} Certificate (by decide)
  decide

theorem node_401 :
    (scheme.enumerateFrom [30, 31, 32] {29, 27, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 27, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 27, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 27, 11} Certificate (by decide)
  decide

theorem node_402 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {27, 11} Certificate (by decide)
    ?_ node_401
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 11} Certificate (by decide)
  decide

theorem node_403 :
    (scheme.enumerateFrom [] {32, 29, 11}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_404 :
    (scheme.enumerateFrom [30, 31, 32] {29, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 11} Certificate (by decide)
    ?_ node_403
  decide

theorem node_405 :
    (scheme.enumerateFrom [] {32, 30, 11}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_406 :
    (scheme.enumerateFrom [31, 32] {30, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 11} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {30, 11} Certificate (by decide)
    ?_ node_405
  decide

theorem node_407 :
    (scheme.enumerateFrom [] {32, 11}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_408 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_387
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_391
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_394
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_397
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_399
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_400
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {11} Certificate (by decide)
    ?_ node_402
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {11} Certificate (by decide)
    ?_ node_404
  apply scheme.check_enumeration_split 30 [31, 32] {11} Certificate (by decide)
    ?_ node_406
  apply scheme.check_enumeration_skip 31 [32] {11} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {11} Certificate (by decide)
    ?_ node_407
  decide

theorem node_409 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {14, 13, 12} Certificate (by decide)
  decide

theorem node_410 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
    ?_ node_409
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 12} Certificate (by decide)
  decide

theorem node_411 :
    (scheme.enumerateFrom [] {32, 14, 12}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_412 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 12} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {14, 12} Certificate (by decide)
    ?_ node_411
  decide

theorem node_413 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 12} Certificate (by decide)
  decide

theorem node_414 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 12} Certificate (by decide)
  decide

theorem node_415 :
    (scheme.enumerateFrom [30, 31, 32] {29, 16, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 16, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 16, 12} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
