module

public import RigidGHZ.Supplement.Periodic.TenCheck01

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem node_64 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 5} Certificate (by decide)
  decide

theorem node_65 :
    (scheme.enumerateFrom [17, 18, 19] {16, 14, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 14, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 14, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 14, 5} Certificate (by decide)
  decide

theorem node_66 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 5} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {14, 5} Certificate (by decide)
    ?_ node_65
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 5} Certificate (by decide)
  decide

theorem node_67 :
    (scheme.enumerateFrom [17, 18, 19] {16, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 5} Certificate (by decide)
  decide

theorem node_68 :
    (scheme.enumerateFrom [] {19, 5}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_69 :
    (scheme.enumerateFrom [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
    ?_ node_62
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
    ?_ node_63
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {5} Certificate (by decide)
    ?_ node_64
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {5} Certificate (by decide)
    ?_ node_66
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {5} Certificate (by decide)
    ?_ node_67
  apply scheme.check_enumeration_skip 17 [18, 19] {5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {5} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {5} Certificate (by decide)
    ?_ node_68
  decide

theorem node_70 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 7, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {10, 7, 6} Certificate (by decide)
  decide

theorem node_71 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 7, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {14, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 7, 6} Certificate (by decide)
  decide

theorem node_72 :
    (scheme.enumerateFrom [19] {18, 7, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 7, 6} Certificate (by decide)
  decide

theorem node_73 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
    ?_ node_70
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {7, 6} Certificate (by decide)
    ?_ node_71
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {7, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {7, 6} Certificate (by decide)
    ?_ node_72
  apply scheme.check_enumeration_skip 19 [] {7, 6} Certificate (by decide)
  decide

theorem node_74 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11, 8, 6} Certificate (by decide)
  decide

theorem node_75 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 8, 6} Certificate (by decide)
  decide

theorem node_76 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
    ?_ node_74
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
    ?_ node_75
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {8, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {8, 6} Certificate (by decide)
  decide

theorem node_77 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 10, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 10, 6} Certificate (by decide)
  decide

theorem node_78 :
    (scheme.enumerateFrom [] {19, 10, 6}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_79 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {10, 6} Certificate (by decide)
    ?_ node_77
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 6} Certificate (by decide)
    ?_ node_78
  decide

theorem node_80 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11, 6} Certificate (by decide)
  decide

theorem node_81 :
    (scheme.enumerateFrom [19] {18, 13, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 13, 6} Certificate (by decide)
  decide

theorem node_82 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 6} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {13, 6} Certificate (by decide)
    ?_ node_81
  apply scheme.check_enumeration_skip 19 [] {13, 6} Certificate (by decide)
  decide

theorem node_83 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {14, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 6} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 6} Certificate (by decide)
  decide

theorem node_84 :
    (scheme.enumerateFrom [19] {18, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 6} Certificate (by decide)
  decide

theorem node_85 :
    (scheme.enumerateFrom [] {19, 6}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_86 :
    (scheme.enumerateFrom [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_73
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_76
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_79
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_80
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_82
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {6} Certificate (by decide)
    ?_ node_83
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {6} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {6} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {6} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {6} Certificate (by decide)
    ?_ node_84
  apply scheme.check_enumeration_split 19 [] {6} Certificate (by decide)
    ?_ node_85
  decide

theorem node_87 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 10, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 10, 7} Certificate (by decide)
  decide

theorem node_88 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15, 10, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {15, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {15, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15, 10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {15, 10, 7} Certificate (by decide)
  decide

theorem node_89 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {10, 7} Certificate (by decide)
    ?_ node_87
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] {10, 7} Certificate (by decide)
    ?_ node_88
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {10, 7} Certificate (by decide)
  decide

theorem node_90 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 7} Certificate (by decide)
  decide

theorem node_91 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {14, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 7} Certificate (by decide)
  decide

theorem node_92 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {15, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {15, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {15, 7} Certificate (by decide)
  decide

theorem node_93 :
    (scheme.enumerateFrom [19] {18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 7} Certificate (by decide)
  decide

theorem node_94 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
    ?_ node_89
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
    ?_ node_90
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {7} Certificate (by decide)
    ?_ node_91
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] {7} Certificate (by decide)
    ?_ node_92
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {7} Certificate (by decide)
    ?_ node_93
  apply scheme.check_enumeration_skip 19 [] {7} Certificate (by decide)
  decide

theorem node_95 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11, 8} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Ten
