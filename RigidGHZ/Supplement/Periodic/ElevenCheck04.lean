module

public import RigidGHZ.Supplement.Periodic.ElevenCheck03

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_128 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 5, 3} Certificate (by decide)
  decide

theorem node_129 :
    (scheme.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
    ?_ node_127
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
    ?_ node_128
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {5, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {5, 3} Certificate (by decide)
  decide

theorem node_130 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 8, 7, 3} Certificate (by decide)
  decide

theorem node_131 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 8, 7, 3} Certificate (by decide)
  decide

theorem node_132 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
    ?_ node_130
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
    ?_ node_131
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {8, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {8, 7, 3} Certificate (by decide)
  decide

theorem node_133 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 7, 3} Certificate (by decide)
  decide

theorem node_134 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 7, 3} Certificate (by decide)
  decide

theorem node_135 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
    ?_ node_132
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
    ?_ node_133
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
    ?_ node_134
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {7, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {7, 3} Certificate (by decide)
  decide

theorem node_136 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 8, 3} Certificate (by decide)
  decide

theorem node_137 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 8, 3} Certificate (by decide)
  decide

theorem node_138 :
    (scheme.enumerateFrom [] {32, 8, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_139 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
    ?_ node_136
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
    ?_ node_137
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {8, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {8, 3} Certificate (by decide)
    ?_ node_138
  decide

theorem node_140 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 11, 3} Certificate (by decide)
  decide

theorem node_141 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 11, 3} Certificate (by decide)
  decide

theorem node_142 :
    (scheme.enumerateFrom [] {32, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_143 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
    ?_ node_140
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
    ?_ node_141
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {11, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {11, 3} Certificate (by decide)
    ?_ node_142
  decide

theorem node_144 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14, 3} Certificate (by decide)
  decide

theorem node_145 :
    (scheme.enumerateFrom [] {32, 14, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_146 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
    ?_ node_144
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {14, 3} Certificate (by decide)
    ?_ node_145
  decide

theorem node_147 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 17, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 17, 3} Certificate (by decide)
  decide

theorem node_148 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
    ?_ node_147
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 17, 3} Certificate (by decide)
  decide

theorem node_149 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 17, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 17, 3} Certificate (by decide)
  decide

theorem node_150 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 17, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 17, 3} Certificate (by decide)
  decide

theorem node_151 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
    ?_ node_148
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
    ?_ node_149
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
    ?_ node_150
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 3} Certificate (by decide)
  decide

theorem node_152 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 19, 3} Certificate (by decide)
  decide

theorem node_153 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
    ?_ node_152
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 19, 3} Certificate (by decide)
  decide

theorem node_154 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 19, 3} Certificate (by decide)
  decide

theorem node_155 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 19, 3} Certificate (by decide)
  decide

theorem node_156 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
    ?_ node_153
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
    ?_ node_154
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
    ?_ node_155
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 3} Certificate (by decide)
  decide

theorem node_157 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 20, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 20, 3} Certificate (by decide)
  decide

theorem node_158 :
    (scheme.enumerateFrom [] {32, 20, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_159 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
    ?_ node_157
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {20, 3} Certificate (by decide)
    ?_ node_158
  decide

end RigidGHZ.Supplement.Periodic.Eleven
