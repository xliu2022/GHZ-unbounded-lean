module

public import RigidGHZ.Supplement.Periodic.LatinCheck01

public import RigidGHZ.Supplement.Periodic.LatinBitData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem row_node_32 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 15, 0} 10797063 256 (by decide) (by decide)]
  decide

theorem row_node_33 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {15, 0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {15, 0} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 0} 16) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 0} 17) hc)
  · exact row_node_28
  · exact row_node_29
  · exact row_node_30
  · exact row_node_31
  · exact row_node_32
  · exact False.elim ((by decide : ¬scheme.Compatible {15, 0} 23) hc)

theorem row_node_34 :
    (scheme.enumerateGroups [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {0}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {0} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact False.elim ((by decide : ¬scheme.Compatible {0} 8) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {0} 9) hc)
  · exact row_node_5
  · exact row_node_11
  · exact row_node_16
  · exact row_node_21
  · exact row_node_27
  · exact row_node_33

theorem row_node_35 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 10, 1} 4784647 1280 (by decide) (by decide)]
  decide

theorem row_node_36 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 10, 1} 591367 1049600 (by decide) (by decide)]
  decide

theorem row_node_37 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 10, 1} 721415 3072 (by decide) (by decide)]
  decide

theorem row_node_38 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {22, 10, 1} 868871 1024 (by decide) (by decide)]
  decide

theorem row_node_39 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 10, 1} 9011719 1024 (by decide) (by decide)]
  decide

theorem row_node_40 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {10, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {10, 1} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_35
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 1} 17) hc)
  · exact row_node_36
  · exact row_node_37
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 1} 20) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 1} 21) hc)
  · exact row_node_38
  · exact row_node_39

theorem row_node_41 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 11, 1} 4524551 256 (by decide) (by decide)]
  decide

theorem row_node_42 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {18, 11, 1} 331271 1048576 (by decide) (by decide)]
  decide

theorem row_node_43 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 11, 1} 461319 2048 (by decide) (by decide)]
  decide

theorem row_node_44 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 11, 1} 858631 0 (by decide) (by decide)]
  decide

theorem row_node_45 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 11, 1} 8751623 0 (by decide) (by decide)]
  decide

theorem row_node_46 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {11, 1}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {11, 1} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_41
  · exact False.elim ((by decide : ¬scheme.Compatible {11, 1} 17) hc)
  · exact row_node_42
  · exact row_node_43
  · exact row_node_44
  · exact False.elim ((by decide : ¬scheme.Compatible {11, 1} 21) hc)
  · exact False.elim ((by decide : ¬scheme.Compatible {11, 1} 22) hc)
  · exact row_node_45

theorem row_node_47 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 1}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 1} 4264455 1048832 (by decide) (by decide)]
  decide

end RigidGHZ.Supplement.Periodic.Latin
