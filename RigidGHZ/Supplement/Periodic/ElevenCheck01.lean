module

public import RigidGHZ.Supplement.Periodic.ElevenCheck00

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_32 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
    ?_ node_27
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
    ?_ node_28
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {11, 0} Certificate (by decide)
    ?_ node_30
  apply scheme.check_enumeration_skip 30 [31, 32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {11, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {11, 0} Certificate (by decide)
    ?_ node_31
  decide

theorem node_33 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14, 0} Certificate (by decide)
  decide

theorem node_34 :
    (scheme.enumerateFrom [] {32, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_35 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
    ?_ node_33
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {14, 0} Certificate (by decide)
    ?_ node_34
  decide

theorem node_36 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 17, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 17, 0} Certificate (by decide)
  decide

theorem node_37 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
    ?_ node_36
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 0} Certificate (by decide)
  decide

theorem node_38 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 19, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 19, 0} Certificate (by decide)
  decide

theorem node_39 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
    ?_ node_38
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 0} Certificate (by decide)
  decide

theorem node_40 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 0} Certificate (by decide)
  decide

theorem node_41 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 0} Certificate (by decide)
    ?_ node_40
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 0} Certificate (by decide)
  decide

theorem node_42 :
    (scheme.enumerateFrom [] {32, 29, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_43 :
    (scheme.enumerateFrom [30, 31, 32] {29, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 0} Certificate (by decide)
    ?_ node_42
  decide

theorem node_44 :
    (scheme.enumerateFrom [] {32, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_45 :
    (scheme.enumerateFrom [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_5
  apply scheme.check_enumeration_split 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_8
  apply scheme.check_enumeration_skip 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_11
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_15
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_22
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_26
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_32
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_35
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_37
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_39
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {0} Certificate (by decide)
    ?_ node_41
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {0} Certificate (by decide)
    ?_ node_43
  apply scheme.check_enumeration_skip 30 [31, 32] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {0} Certificate (by decide)
    ?_ node_44
  decide

theorem node_46 :
    (scheme.enumerateFrom [] {32, 3, 2, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_47 :
    (scheme.enumerateFrom [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {3, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {3, 2, 1} Certificate (by decide)
    ?_ node_46
  decide

theorem node_48 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {9, 2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {9, 2, 1} Certificate (by decide)
  decide

theorem node_49 :
    (scheme.enumerateFrom [] {32, 2, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_50 :
    (scheme.enumerateFrom [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
    ?_ node_47
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
    ?_ node_48
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {2, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {2, 1} Certificate (by decide)
    ?_ node_49
  decide

theorem node_51 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 3, 1} Certificate (by decide)
  decide

theorem node_52 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 3, 1} Certificate (by decide)
  decide

theorem node_53 :
    (scheme.enumerateFrom [] {32, 3, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_54 :
    (scheme.enumerateFrom [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
    ?_ node_51
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
    ?_ node_52
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {3, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {3, 1} Certificate (by decide)
    ?_ node_53
  decide

theorem node_55 :
    (scheme.enumerateFrom [] {32, 6, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_56 :
    (scheme.enumerateFrom [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {6, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {6, 1} Certificate (by decide)
    ?_ node_55
  decide

theorem node_57 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {10, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {10, 9, 1} Certificate (by decide)
  decide

theorem node_58 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 9, 1} Certificate (by decide)
  decide

theorem node_59 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 9, 1} Certificate (by decide)
  decide

theorem node_60 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
    ?_ node_58
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
    ?_ node_59
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 9, 1} Certificate (by decide)
  decide

theorem node_61 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 9, 1} Certificate (by decide)
  decide

theorem node_62 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 9, 1} Certificate (by decide)
  decide

theorem node_63 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 9, 1} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
