module

public import RigidGHZ.Supplement.Periodic.LatinCheck00

public import RigidGHZ.Supplement.Periodic.LatinBitData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem row_node_16 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 0} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 0} 16) hc)
  · exact row_node_12
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 0} 18) hc)
  · exact row_node_13
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 0} 20) hc)
  · exact row_node_14
  · exact row_node_15
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 0} 23) hc)

theorem row_node_17 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 0} 10625543 256 (by decide) (by decide)]
  decide

theorem row_node_18 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 13, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 13, 0} 8528903 1048832 (by decide) (by decide)]
  decide

theorem row_node_19 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 13, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 13, 0} 9056263 256 (by decide) (by decide)]
  decide

theorem row_node_20 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 13, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 13, 0} 8806407 256 (by decide) (by decide)]
  decide

theorem row_node_21 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {13, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {13, 0} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {13, 0} 16) hc)
  · exact row_node_17
  · exact row_node_18
  · exact False.elim ((by decide : ¬scheme.Compatible {13, 0} 19) hc)
  · exact row_node_19
  · exact False.elim ((by decide : ¬scheme.Compatible {13, 0} 21) hc)
  · exact row_node_20
  · exact False.elim ((by decide : ¬scheme.Compatible {13, 0} 23) hc)

theorem row_node_22 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 14, 0} 14696967 256 (by decide) (by decide)]
  decide

theorem row_node_23 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 14, 0} 12600327 1048832 (by decide) (by decide)]
  decide

theorem row_node_24 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 14, 0} 12730375 2304 (by decide) (by decide)]
  decide

theorem row_node_25 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 14, 0} 13127687 256 (by decide) (by decide)]
  decide

theorem row_node_26 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 14, 0} 12673031 256 (by decide) (by decide)]
  decide

theorem row_node_27 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {14, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {14, 0} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {14, 0} 16) hc)
  · exact row_node_22
  · exact row_node_23
  · exact row_node_24
  · exact row_node_25
  · exact row_node_26
  · exact False.elim ((by decide : ¬scheme.Compatible {14, 0} 22) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {14, 0} 23) hc)

theorem row_node_28 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 15, 0} 10519559 1048832 (by decide) (by decide)]
  decide

theorem row_node_29 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 15, 0} 10649607 2304 (by decide) (by decide)]
  decide

theorem row_node_30 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 15, 0} 11046919 256 (by decide) (by decide)]
  decide

theorem row_node_31 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 15, 0} 10592263 256 (by decide) (by decide)]
  decide

end RigidGHZ.Supplement.Periodic.Latin
