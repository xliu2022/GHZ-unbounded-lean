module

public import RigidGHZ.Supplement.Periodic.ElevenCheck01

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_64 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
    ?_ node_57
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
    ?_ node_60
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
    ?_ node_61
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
    ?_ node_62
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
    ?_ node_63
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {9, 1} Certificate (by decide)
  decide

theorem node_65 :
    (scheme.enumerateFrom [] {32, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_66 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {10, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {10, 1} Certificate (by decide)
    ?_ node_65
  decide

theorem node_67 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 12, 1} Certificate (by decide)
  decide

theorem node_68 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 12, 1} Certificate (by decide)
  decide

theorem node_69 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
    ?_ node_67
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
    ?_ node_68
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {16, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 12, 1} Certificate (by decide)
  decide

theorem node_70 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 12, 1} Certificate (by decide)
  decide

theorem node_71 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 12, 1} Certificate (by decide)
  decide

theorem node_72 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 12, 1} Certificate (by decide)
  decide

theorem node_73 :
    (scheme.enumerateFrom [] {32, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_74 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
    ?_ node_69
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
    ?_ node_70
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
    ?_ node_71
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
    ?_ node_72
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {12, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {12, 1} Certificate (by decide)
    ?_ node_73
  decide

theorem node_75 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17, 16, 1} Certificate (by decide)
  decide

theorem node_76 :
    (scheme.enumerateFrom [31, 32] {30, 17, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17, 16, 1} Certificate (by decide)
  decide

theorem node_77 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
    ?_ node_75
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17, 16, 1} Certificate (by decide)
    ?_ node_76
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 1} Certificate (by decide)
  decide

theorem node_78 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18, 16, 1} Certificate (by decide)
  decide

theorem node_79 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
    ?_ node_78
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 16, 1} Certificate (by decide)
  decide

theorem node_80 :
    (scheme.enumerateFrom [31, 32] {30, 19, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19, 16, 1} Certificate (by decide)
  decide

theorem node_81 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19, 16, 1} Certificate (by decide)
    ?_ node_80
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 1} Certificate (by decide)
  decide

theorem node_82 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 16, 1} Certificate (by decide)
  decide

theorem node_83 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 16, 1} Certificate (by decide)
  decide

theorem node_84 :
    (scheme.enumerateFrom [31, 32] {30, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 16, 1} Certificate (by decide)
  decide

theorem node_85 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
    ?_ node_77
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
    ?_ node_79
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
    ?_ node_81
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
    ?_ node_82
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {16, 1} Certificate (by decide)
    ?_ node_83
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {16, 1} Certificate (by decide)
    ?_ node_84
  apply scheme.check_enumeration_skip 31 [32] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 1} Certificate (by decide)
  decide

theorem node_86 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17, 1} Certificate (by decide)
  decide

theorem node_87 :
    (scheme.enumerateFrom [31, 32] {30, 17, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17, 1} Certificate (by decide)
  decide

theorem node_88 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
    ?_ node_86
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17, 1} Certificate (by decide)
    ?_ node_87
  apply scheme.check_enumeration_skip 31 [32] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 1} Certificate (by decide)
  decide

theorem node_89 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18, 1} Certificate (by decide)
  decide

theorem node_90 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 18, 1} Certificate (by decide)
  decide

theorem node_91 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
    ?_ node_89
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
    ?_ node_90
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 1} Certificate (by decide)
  decide

theorem node_92 :
    (scheme.enumerateFrom [31, 32] {30, 19, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19, 1} Certificate (by decide)
  decide

theorem node_93 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19, 1} Certificate (by decide)
    ?_ node_92
  apply scheme.check_enumeration_skip 31 [32] {19, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 1} Certificate (by decide)
  decide

theorem node_94 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 21, 1} Certificate (by decide)
  decide

theorem node_95 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
    ?_ node_94
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 1} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
