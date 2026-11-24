module

public import RigidGHZ.Supplement.Periodic.ElevenCheck19C

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_632 :
    (scheme.enumerateFrom [] {32, 31, 30}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_633 :
    (scheme.enumerateFrom [32] {31, 30}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 32 [] {31, 30} Certificate (by decide)
    ?_ node_632
  decide

theorem node_634 :
    (scheme.enumerateFrom [] {32, 30}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_635 :
    (scheme.enumerateFrom [31, 32] {30}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 31 [32] {30} Certificate (by decide)
    ?_ node_633
  apply scheme.check_enumeration_split 32 [] {30} Certificate (by decide)
    ?_ node_634
  decide

theorem node_636 :
    (scheme.enumerateFrom [] {32, 31}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_637 :
    (scheme.enumerateFrom [32] {31}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 32 [] {31} Certificate (by decide)
    ?_ node_636
  decide

theorem node_638 :
    (scheme.enumerateFrom [] {32}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_639 :
    (scheme.enumerateFrom [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_45
  apply scheme.check_enumeration_split 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_102
  apply scheme.check_enumeration_split 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_121
  apply scheme.check_enumeration_split 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_164
  apply scheme.check_enumeration_split 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_218
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_233
  apply scheme.check_enumeration_split 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_247
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_311
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_334
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_371
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_380
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_408
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_430
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_452
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_459
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_481
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_504
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_526
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_540
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_558
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_570
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_581
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_592
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_598
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_607
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_613
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_618
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_623
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] ∅ Certificate (by decide)
    ?_ node_629
  apply scheme.check_enumeration_split 29 [30, 31, 32] ∅ Certificate (by decide)
    ?_ node_631
  apply scheme.check_enumeration_split 30 [31, 32] ∅ Certificate (by decide)
    ?_ node_635
  apply scheme.check_enumeration_split 31 [32] ∅ Certificate (by decide)
    ?_ node_637
  apply scheme.check_enumeration_split 32 [] ∅ Certificate (by decide)
    ?_ node_638
  decide

end RigidGHZ.Supplement.Periodic.Eleven
