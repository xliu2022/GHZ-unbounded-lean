module

public import RigidGHZ.Supplement.Periodic.LatinCheck13

public import RigidGHZ.Supplement.Periodic.LatinBitData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem row_node_224 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 15, 5}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 15, 5} 2663431 1048576 (by decide) (by decide)]
  decide

theorem row_node_225 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 15, 5}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 15, 5} 2793479 2048 (by decide) (by decide)]
  decide

theorem row_node_226 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 15, 5}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 15, 5} 2940935 0 (by decide) (by decide)]
  decide

theorem row_node_227 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {15, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {15, 5} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_223
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 5} 17) hc)
  · exact row_node_224
  · exact row_node_225
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 5} 20) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 5} 21) hc)
  · exact row_node_226
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 5} 23) hc)

theorem row_node_228 :
    (scheme.enumerateGroups [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {5} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_200
  · exact row_node_205
  · exact False.elim ((by decide : ¬scheme.Compatible {5} 10) hc)
  · exact row_node_211
  · exact row_node_217
  · exact False.elim ((by decide : ¬scheme.Compatible {5} 13) hc)
  · exact row_node_222
  · exact row_node_227

theorem row_node_229 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 8, 6} 2180103 1048832 (by decide) (by decide)]
  decide

theorem row_node_230 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 8, 6} 2310151 2304 (by decide) (by decide)]
  decide

theorem row_node_231 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 8, 6} 2707463 256 (by decide) (by decide)]
  decide

theorem row_node_232 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 8, 6} 10600455 256 (by decide) (by decide)]
  decide

theorem row_node_233 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {8, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {8, 6} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {8, 6} 16) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {8, 6} 17) hc)
  · exact row_node_229
  · exact row_node_230
  · exact row_node_231
  · exact False.elim ((by decide : ¬scheme.Compatible {8, 6} 21) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {8, 6} 22) hc)
  · exact row_node_232

theorem row_node_234 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 9, 6} 14696967 256 (by decide) (by decide)]
  decide

theorem row_node_235 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 9, 6} 10503687 1048576 (by decide) (by decide)]
  decide

theorem row_node_236 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 9, 6} 10633735 2048 (by decide) (by decide)]
  decide

theorem row_node_237 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 9, 6} 11031047 0 (by decide) (by decide)]
  decide

theorem row_node_238 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 9, 6} 10576391 0 (by decide) (by decide)]
  decide

theorem row_node_239 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {9, 6}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {9, 6} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_234
  · exact False.elim ((by decide : ¬scheme.Compatible {9, 6} 17) hc)
  · exact row_node_235
  · exact row_node_236
  · exact row_node_237
  · exact row_node_238
  · exact False.elim ((by decide : ¬scheme.Compatible {9, 6} 22) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {9, 6} 23) hc)

end RigidGHZ.Supplement.Periodic.Latin
