module

public import RigidGHZ.Supplement.Periodic.LatinCheck07

public import RigidGHZ.Supplement.Periodic.LatinBitData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem row_node_128 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 11, 3} 5507079 2304 (by decide) (by decide)]
  decide

theorem row_node_129 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 11, 3} 3410439 2048 (by decide) (by decide)]
  decide

theorem row_node_130 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 11, 3} 1313799 1050624 (by decide) (by decide)]
  decide

theorem row_node_131 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 11, 3} 1841159 2048 (by decide) (by decide)]
  decide

theorem row_node_132 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 11, 3} 1386503 2048 (by decide) (by decide)]
  decide

theorem row_node_133 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 11, 3} 9734151 2048 (by decide) (by decide)]
  decide

theorem row_node_134 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {11, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {11, 3} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_128
  · exact row_node_129
  · exact row_node_130
  · exact False.elim ((by decide : ¬scheme.Compatible {11, 3} 19) hc)
  · exact row_node_131
  · exact row_node_132
  · exact False.elim ((by decide : ¬scheme.Compatible {11, 3} 22) hc)
  · exact row_node_133

theorem row_node_135 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 3} 5246983 1050880 (by decide) (by decide)]
  decide

theorem row_node_136 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 12, 3} 3150343 1050624 (by decide) (by decide)]
  decide

theorem row_node_137 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 12, 3} 1126407 1050624 (by decide) (by decide)]
  decide

theorem row_node_138 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 12, 3} 1331207 1050624 (by decide) (by decide)]
  decide

theorem row_node_139 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 12, 3} 9474055 1050624 (by decide) (by decide)]
  decide

theorem row_node_140 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 3}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 3} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_135
  · exact row_node_136
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 3} 18) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 3} 19) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 3} 20) hc)
  · exact row_node_137
  · exact row_node_138
  · exact row_node_139

theorem row_node_141 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 13, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 13, 3} 5382151 2304 (by decide) (by decide)]
  decide

theorem row_node_142 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 3} 3285511 2048 (by decide) (by decide)]
  decide

theorem row_node_143 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 13, 3}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 13, 3} 1188871 1050624 (by decide) (by decide)]
  decide

end RigidGHZ.Supplement.Periodic.Latin
