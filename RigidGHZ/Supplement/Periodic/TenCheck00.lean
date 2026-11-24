module

public import RigidGHZ.Supplement.Periodic.TenData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem node_0 :
    (scheme.enumerateFrom [] {19, 5, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_1 :
    (scheme.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {5, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {5, 0} Certificate (by decide)
    ?_ node_0
  decide

theorem node_2 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 7, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {10, 7, 0} Certificate (by decide)
  decide

theorem node_3 :
    (scheme.enumerateFrom [19] {18, 7, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 7, 0} Certificate (by decide)
  decide

theorem node_4 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
    ?_ node_2
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {7, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {7, 0} Certificate (by decide)
    ?_ node_3
  apply scheme.check_enumeration_skip 19 [] {7, 0} Certificate (by decide)
  decide

theorem node_5 :
    (scheme.enumerateFrom [18, 19] {17, 8, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 8, 0} Certificate (by decide)
  decide

theorem node_6 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19] {8, 0} Certificate (by decide)
    ?_ node_5
  apply scheme.check_enumeration_skip 18 [19] {8, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {8, 0} Certificate (by decide)
  decide

theorem node_7 :
    (scheme.enumerateFrom [] {19, 10, 9, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_8 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 9, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 9, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 9, 0} Certificate (by decide)
    ?_ node_7
  decide

theorem node_9 :
    (scheme.enumerateFrom [] {19, 9, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_10 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {9, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {9, 0} Certificate (by decide)
    ?_ node_8
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {9, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {9, 0} Certificate (by decide)
    ?_ node_9
  decide

theorem node_11 :
    (scheme.enumerateFrom [] {19, 10, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_12 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 0} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 0} Certificate (by decide)
    ?_ node_11
  decide

theorem node_13 :
    (scheme.enumerateFrom [18, 19] {17, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 0} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 0} Certificate (by decide)
  decide

theorem node_14 :
    (scheme.enumerateFrom [19] {18, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 0} Certificate (by decide)
  decide

theorem node_15 :
    (scheme.enumerateFrom [] {19, 0}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_16 :
    (scheme.enumerateFrom [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
    ?_ node_1
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
    ?_ node_4
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
    ?_ node_6
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
    ?_ node_10
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
    ?_ node_12
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {0} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19] {0} Certificate (by decide)
    ?_ node_13
  apply scheme.check_enumeration_split 18 [19] {0} Certificate (by decide)
    ?_ node_14
  apply scheme.check_enumeration_split 19 [] {0} Certificate (by decide)
    ?_ node_15
  decide

theorem node_17 :
    (scheme.enumerateFrom [17, 18, 19] {16, 5, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 5, 1} Certificate (by decide)
  decide

theorem node_18 :
    (scheme.enumerateFrom [] {19, 5, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_19 :
    (scheme.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {5, 1} Certificate (by decide)
    ?_ node_17
  apply scheme.check_enumeration_skip 17 [18, 19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {5, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {5, 1} Certificate (by decide)
    ?_ node_18
  decide

theorem node_20 :
    (scheme.enumerateFrom [19] {18, 7, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 7, 1} Certificate (by decide)
  decide

theorem node_21 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {7, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {7, 1} Certificate (by decide)
    ?_ node_20
  apply scheme.check_enumeration_skip 19 [] {7, 1} Certificate (by decide)
  decide

theorem node_22 :
    (scheme.enumerateFrom [17, 18, 19] {16, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 9, 1} Certificate (by decide)
  decide

theorem node_23 :
    (scheme.enumerateFrom [] {19, 9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_24 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {9, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {9, 1} Certificate (by decide)
    ?_ node_22
  apply scheme.check_enumeration_skip 17 [18, 19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {9, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {9, 1} Certificate (by decide)
    ?_ node_23
  decide

theorem node_25 :
    (scheme.enumerateFrom [19] {18, 16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 16, 1} Certificate (by decide)
  decide

theorem node_26 :
    (scheme.enumerateFrom [17, 18, 19] {16, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 1} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {16, 1} Certificate (by decide)
    ?_ node_25
  apply scheme.check_enumeration_skip 19 [] {16, 1} Certificate (by decide)
  decide

theorem node_27 :
    (scheme.enumerateFrom [18, 19] {17, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 1} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 1} Certificate (by decide)
  decide

theorem node_28 :
    (scheme.enumerateFrom [19] {18, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 1} Certificate (by decide)
  decide

theorem node_29 :
    (scheme.enumerateFrom [] {19, 1}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_30 :
    (scheme.enumerateFrom [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
    ?_ node_19
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
    ?_ node_21
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
    ?_ node_24
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {1} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {1} Certificate (by decide)
    ?_ node_26
  apply scheme.check_enumeration_split 17 [18, 19] {1} Certificate (by decide)
    ?_ node_27
  apply scheme.check_enumeration_split 18 [19] {1} Certificate (by decide)
    ?_ node_28
  apply scheme.check_enumeration_split 19 [] {1} Certificate (by decide)
    ?_ node_29
  decide

theorem node_31 :
    (scheme.enumerateFrom [] {19, 10, 6, 2}).all
      (fun A => decide (Certificate A)) = true := by
  decide

end RigidGHZ.Supplement.Periodic.Ten
