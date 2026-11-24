module

public import RigidGHZ.Supplement.Periodic.TenCheck00

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem node_32 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 6, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 6, 2} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 6, 2} Certificate (by decide)
    ?_ node_31
  decide

theorem node_33 :
    (scheme.enumerateFrom [] {19, 6, 2}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_34 :
    (scheme.enumerateFrom [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
    ?_ node_32
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {6, 2} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {6, 2} Certificate (by decide)
    ?_ node_33
  decide

theorem node_35 :
    (scheme.enumerateFrom [17, 18, 19] {16, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 10, 2} Certificate (by decide)
  decide

theorem node_36 :
    (scheme.enumerateFrom [] {19, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_37 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {10, 2} Certificate (by decide)
    ?_ node_35
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 2} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 2} Certificate (by decide)
    ?_ node_36
  decide

theorem node_38 :
    (scheme.enumerateFrom [17, 18, 19] {16, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 2} Certificate (by decide)
  decide

theorem node_39 :
    (scheme.enumerateFrom [18, 19] {17, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 2} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 2} Certificate (by decide)
  decide

theorem node_40 :
    (scheme.enumerateFrom [] {19, 2}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_41 :
    (scheme.enumerateFrom [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_split 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
    ?_ node_34
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
    ?_ node_37
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {2} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {2} Certificate (by decide)
    ?_ node_38
  apply scheme.check_enumeration_split 17 [18, 19] {2} Certificate (by decide)
    ?_ node_39
  apply scheme.check_enumeration_skip 18 [19] {2} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {2} Certificate (by decide)
    ?_ node_40
  decide

theorem node_42 :
    (scheme.enumerateFrom [17, 18, 19] {16, 10, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 10, 3} Certificate (by decide)
  decide

theorem node_43 :
    (scheme.enumerateFrom [] {19, 10, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_44 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {10, 3} Certificate (by decide)
    ?_ node_42
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 3} Certificate (by decide)
    ?_ node_43
  decide

theorem node_45 :
    (scheme.enumerateFrom [19] {18, 16, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 16, 3} Certificate (by decide)
  decide

theorem node_46 :
    (scheme.enumerateFrom [17, 18, 19] {16, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 3} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {16, 3} Certificate (by decide)
    ?_ node_45
  apply scheme.check_enumeration_skip 19 [] {16, 3} Certificate (by decide)
  decide

theorem node_47 :
    (scheme.enumerateFrom [19] {18, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 3} Certificate (by decide)
  decide

theorem node_48 :
    (scheme.enumerateFrom [] {19, 3}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_49 :
    (scheme.enumerateFrom [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
    ?_ node_44
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {3} Certificate (by decide)
    ?_ node_46
  apply scheme.check_enumeration_skip 17 [18, 19] {3} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {3} Certificate (by decide)
    ?_ node_47
  apply scheme.check_enumeration_split 19 [] {3} Certificate (by decide)
    ?_ node_48
  decide

theorem node_50 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11, 4} Certificate (by decide)
  decide

theorem node_51 :
    (scheme.enumerateFrom [19] {18, 13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 13, 4} Certificate (by decide)
  decide

theorem node_52 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {13, 4} Certificate (by decide)
    ?_ node_51
  apply scheme.check_enumeration_skip 19 [] {13, 4} Certificate (by decide)
  decide

theorem node_53 :
    (scheme.enumerateFrom [] {19, 15, 4}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_54 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {15, 4} Certificate (by decide)
    ?_ node_53
  decide

theorem node_55 :
    (scheme.enumerateFrom [18, 19] {17, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 4} Certificate (by decide)
  decide

theorem node_56 :
    (scheme.enumerateFrom [19] {18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 4} Certificate (by decide)
  decide

theorem node_57 :
    (scheme.enumerateFrom [] {19, 4}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_58 :
    (scheme.enumerateFrom [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
    ?_ node_50
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {4} Certificate (by decide)
    ?_ node_52
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] {4} Certificate (by decide)
    ?_ node_54
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19] {4} Certificate (by decide)
    ?_ node_55
  apply scheme.check_enumeration_split 18 [19] {4} Certificate (by decide)
    ?_ node_56
  apply scheme.check_enumeration_split 19 [] {4} Certificate (by decide)
    ?_ node_57
  decide

theorem node_59 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 6, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 6, 5} Certificate (by decide)
  decide

theorem node_60 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 6, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {14, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 6, 5} Certificate (by decide)
  decide

theorem node_61 :
    (scheme.enumerateFrom [] {19, 6, 5}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_62 :
    (scheme.enumerateFrom [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
    ?_ node_59
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {6, 5} Certificate (by decide)
    ?_ node_60
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {6, 5} Certificate (by decide)
    ?_ node_61
  decide

theorem node_63 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 5} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Ten
