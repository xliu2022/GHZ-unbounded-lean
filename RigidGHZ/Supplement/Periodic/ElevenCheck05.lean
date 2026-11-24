module

public import RigidGHZ.Supplement.Periodic.ElevenCheck04

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_160 :
    (scheme.enumerateFrom [] {32, 23, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_161 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {23, 3} Certificate (by decide)
    ?_ node_160
  decide

theorem node_162 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 3} Certificate (by decide)
  decide

theorem node_163 :
    (scheme.enumerateFrom [] {32, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_164 :
    (scheme.enumerateFrom [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_126
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_129
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_135
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_139
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_143
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_146
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_151
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_156
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_159
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_161
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {3} Certificate (by decide)
    ?_ node_162
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {3} Certificate (by decide)
    ?_ node_163
  decide

theorem node_165 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 5, 4} Certificate (by decide)
  decide

theorem node_166 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 5, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 5, 4} Certificate (by decide)
  decide

theorem node_167 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 5, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 5, 4} Certificate (by decide)
  decide

theorem node_168 :
    (scheme.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
    ?_ node_165
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
    ?_ node_166
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
    ?_ node_167
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {5, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {5, 4} Certificate (by decide)
  decide

theorem node_169 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {9, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {9, 8, 4} Certificate (by decide)
  decide

theorem node_170 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 8, 4} Certificate (by decide)
  decide

theorem node_171 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 8, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 8, 4} Certificate (by decide)
  decide

theorem node_172 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 8, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 8, 4} Certificate (by decide)
  decide

theorem node_173 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
    ?_ node_169
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
    ?_ node_170
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
    ?_ node_171
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {8, 4} Certificate (by decide)
    ?_ node_172
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {8, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {8, 4} Certificate (by decide)
  decide

theorem node_174 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 9, 4} Certificate (by decide)
  decide

theorem node_175 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 9, 4} Certificate (by decide)
  decide

theorem node_176 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 9, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 9, 4} Certificate (by decide)
  decide

theorem node_177 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
    ?_ node_174
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
    ?_ node_175
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
    ?_ node_176
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {9, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {9, 4} Certificate (by decide)
  decide

theorem node_178 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 12, 4} Certificate (by decide)
  decide

theorem node_179 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 12, 4} Certificate (by decide)
  decide

theorem node_180 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 12, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 12, 4} Certificate (by decide)
  decide

theorem node_181 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
    ?_ node_178
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
    ?_ node_179
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
    ?_ node_180
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {12, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {12, 4} Certificate (by decide)
  decide

theorem node_182 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 13, 4} Certificate (by decide)
  decide

theorem node_183 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 18, 13, 4} Certificate (by decide)
  decide

theorem node_184 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
    ?_ node_183
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 13, 4} Certificate (by decide)
  decide

theorem node_185 :
    (scheme.enumerateFrom [31, 32] {30, 20, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 20, 13, 4} Certificate (by decide)
  decide

theorem node_186 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {20, 13, 4} Certificate (by decide)
    ?_ node_185
  apply scheme.check_enumeration_skip 31 [32] {20, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 13, 4} Certificate (by decide)
  decide

theorem node_187 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 13, 4} Certificate (by decide)
  decide

theorem node_188 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 13, 4} Certificate (by decide)
  decide

theorem node_189 :
    (scheme.enumerateFrom [31, 32] {30, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 13, 4} Certificate (by decide)
  decide

theorem node_190 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
    ?_ node_182
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
    ?_ node_184
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
    ?_ node_186
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
    ?_ node_187
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
    ?_ node_188
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {13, 4} Certificate (by decide)
    ?_ node_189
  apply scheme.check_enumeration_skip 31 [32] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 4} Certificate (by decide)
  decide

theorem node_191 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 15, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 15, 4} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
