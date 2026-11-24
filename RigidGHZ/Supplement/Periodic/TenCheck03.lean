module

public import RigidGHZ.Supplement.Periodic.TenCheck02

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem node_96 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 8} Certificate (by decide)
  decide

theorem node_97 :
    (scheme.enumerateFrom [17, 18, 19] {16, 15, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 15, 8} Certificate (by decide)
  decide

theorem node_98 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 16 [17, 18, 19] {15, 8} Certificate (by decide)
    ?_ node_97
  apply scheme.check_enumeration_skip 17 [18, 19] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {15, 8} Certificate (by decide)
  decide

theorem node_99 :
    (scheme.enumerateFrom [17, 18, 19] {16, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 8} Certificate (by decide)
  decide

theorem node_100 :
    (scheme.enumerateFrom [18, 19] {17, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 8} Certificate (by decide)
  decide

theorem node_101 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] {8} Certificate (by decide)
    ?_ node_95
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {8} Certificate (by decide)
    ?_ node_96
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] {8} Certificate (by decide)
    ?_ node_98
  apply scheme.check_enumeration_split 16 [17, 18, 19] {8} Certificate (by decide)
    ?_ node_99
  apply scheme.check_enumeration_split 17 [18, 19] {8} Certificate (by decide)
    ?_ node_100
  apply scheme.check_enumeration_skip 18 [19] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {8} Certificate (by decide)
  decide

theorem node_102 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 10, 9} Certificate (by decide)
  decide

theorem node_103 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 10, 9} Certificate (by decide)
  decide

theorem node_104 :
    (scheme.enumerateFrom [17, 18, 19] {16, 10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 10, 9} Certificate (by decide)
  decide

theorem node_105 :
    (scheme.enumerateFrom [] {19, 10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_106 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {10, 9} Certificate (by decide)
    ?_ node_102
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {10, 9} Certificate (by decide)
    ?_ node_103
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {10, 9} Certificate (by decide)
    ?_ node_104
  apply scheme.check_enumeration_skip 17 [18, 19] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10, 9} Certificate (by decide)
    ?_ node_105
  decide

theorem node_107 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11, 9} Certificate (by decide)
  decide

theorem node_108 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 9} Certificate (by decide)
  decide

theorem node_109 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 9} Certificate (by decide)
  decide

theorem node_110 :
    (scheme.enumerateFrom [17, 18, 19] {16, 14, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 14, 9} Certificate (by decide)
  decide

theorem node_111 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {14, 9} Certificate (by decide)
    ?_ node_110
  apply scheme.check_enumeration_skip 17 [18, 19] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14, 9} Certificate (by decide)
  decide

theorem node_112 :
    (scheme.enumerateFrom [17, 18, 19] {16, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 9} Certificate (by decide)
  decide

theorem node_113 :
    (scheme.enumerateFrom [] {19, 9}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_114 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] {9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] {9} Certificate (by decide)
    ?_ node_106
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] {9} Certificate (by decide)
    ?_ node_107
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {9} Certificate (by decide)
    ?_ node_108
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {9} Certificate (by decide)
    ?_ node_109
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] {9} Certificate (by decide)
    ?_ node_111
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {9} Certificate (by decide)
    ?_ node_112
  apply scheme.check_enumeration_skip 17 [18, 19] {9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {9} Certificate (by decide)
    ?_ node_113
  decide

theorem node_115 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {12, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12, 10} Certificate (by decide)
  decide

theorem node_116 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {13, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {13, 10} Certificate (by decide)
  decide

theorem node_117 :
    (scheme.enumerateFrom [17, 18, 19] {16, 15, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 15, 10} Certificate (by decide)
  decide

theorem node_118 :
    (scheme.enumerateFrom [] {19, 15, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_119 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 16 [17, 18, 19] {15, 10} Certificate (by decide)
    ?_ node_117
  apply scheme.check_enumeration_skip 17 [18, 19] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {15, 10} Certificate (by decide)
    ?_ node_118
  decide

theorem node_120 :
    (scheme.enumerateFrom [17, 18, 19] {16, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 10} Certificate (by decide)
  decide

theorem node_121 :
    (scheme.enumerateFrom [] {19, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_122 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19] {10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] {10} Certificate (by decide)
    ?_ node_115
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] {10} Certificate (by decide)
    ?_ node_116
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] {10} Certificate (by decide)
    ?_ node_119
  apply scheme.check_enumeration_split 16 [17, 18, 19] {10} Certificate (by decide)
    ?_ node_120
  apply scheme.check_enumeration_skip 17 [18, 19] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {10} Certificate (by decide)
    ?_ node_121
  decide

theorem node_123 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19] {11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {11} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {11} Certificate (by decide)
  decide

theorem node_124 :
    (scheme.enumerateFrom [18, 19] {17, 12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 12} Certificate (by decide)
  decide

theorem node_125 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19] {12}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {12} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19] {12} Certificate (by decide)
    ?_ node_124
  apply scheme.check_enumeration_skip 18 [19] {12} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {12} Certificate (by decide)
  decide

theorem node_126 :
    (scheme.enumerateFrom [19] {18, 13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 13} Certificate (by decide)
  decide

theorem node_127 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19] {13}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19] {13} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19] {13} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {13} Certificate (by decide)
    ?_ node_126
  apply scheme.check_enumeration_skip 19 [] {13} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Ten
