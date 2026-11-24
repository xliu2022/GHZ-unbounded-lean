module

public import RigidGHZ.Supplement.Periodic.TenCheck03

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem node_128 :
    (scheme.enumerateFrom [17, 18, 19] {16, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 14} Certificate (by decide)
  decide

theorem node_129 :
    (scheme.enumerateFrom [18, 19] {17, 14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17, 14} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17, 14} Certificate (by decide)
  decide

theorem node_130 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19] {14}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19] {14} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19] {14} Certificate (by decide)
    ?_ node_128
  apply scheme.check_enumeration_split 17 [18, 19] {14} Certificate (by decide)
    ?_ node_129
  apply scheme.check_enumeration_skip 18 [19] {14} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {14} Certificate (by decide)
  decide

theorem node_131 :
    (scheme.enumerateFrom [17, 18, 19] {16, 15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {16, 15} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {16, 15} Certificate (by decide)
  decide

theorem node_132 :
    (scheme.enumerateFrom [] {19, 15}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_133 :
    (scheme.enumerateFrom [16, 17, 18, 19] {15}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 16 [17, 18, 19] {15} Certificate (by decide)
    ?_ node_131
  apply scheme.check_enumeration_skip 17 [18, 19] {15} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19] {15} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [] {15} Certificate (by decide)
    ?_ node_132
  decide

theorem node_134 :
    (scheme.enumerateFrom [19] {18, 16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18, 16} Certificate (by decide)
  decide

theorem node_135 :
    (scheme.enumerateFrom [17, 18, 19] {16}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 17 [18, 19] {16} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19] {16} Certificate (by decide)
    ?_ node_134
  apply scheme.check_enumeration_skip 19 [] {16} Certificate (by decide)
  decide

theorem node_136 :
    (scheme.enumerateFrom [18, 19] {17}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19] {17} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [] {17} Certificate (by decide)
  decide

theorem node_137 :
    (scheme.enumerateFrom [19] {18}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [] {18} Certificate (by decide)
  decide

theorem node_138 :
    (scheme.enumerateFrom [] {19}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_139 :
    (scheme.enumerateFrom [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 0 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_16
  apply scheme.check_enumeration_split 1 [2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_30
  apply scheme.check_enumeration_split 2 [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_41
  apply scheme.check_enumeration_split 3 [4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_49
  apply scheme.check_enumeration_split 4 [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_58
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_69
  apply scheme.check_enumeration_split 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_86
  apply scheme.check_enumeration_split 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_94
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_101
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_114
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_122
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_123
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_125
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_127
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_130
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19] ∅ Certificate (by decide)
    ?_ node_133
  apply scheme.check_enumeration_split 16 [17, 18, 19] ∅ Certificate (by decide)
    ?_ node_135
  apply scheme.check_enumeration_split 17 [18, 19] ∅ Certificate (by decide)
    ?_ node_136
  apply scheme.check_enumeration_split 18 [19] ∅ Certificate (by decide)
    ?_ node_137
  apply scheme.check_enumeration_split 19 [] ∅ Certificate (by decide)
    ?_ node_138
  decide

end RigidGHZ.Supplement.Periodic.Ten
