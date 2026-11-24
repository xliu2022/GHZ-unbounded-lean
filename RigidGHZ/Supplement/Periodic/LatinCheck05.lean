module

public import RigidGHZ.Supplement.Periodic.LatinCheck04

public import RigidGHZ.Supplement.Periodic.LatinBitData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem row_node_80 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 10, 2} 4981767 1280 (by decide) (by decide)]
  decide

theorem row_node_81 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 10, 2} 2885127 1024 (by decide) (by decide)]
  decide

theorem row_node_82 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 10, 2} 918535 3072 (by decide) (by decide)]
  decide

theorem row_node_83 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 10, 2} 861191 1024 (by decide) (by decide)]
  decide

theorem row_node_84 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 10, 2} 9208839 1024 (by decide) (by decide)]
  decide

theorem row_node_85 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {10, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {10, 2} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_80
  · exact row_node_81
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 2} 18) hc)
  · exact row_node_82
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 2} 20) hc)
  · exact row_node_83
  · exact False.elim ((by decide : ¬scheme.Compatible {10, 2} 22) hc)
  · exact row_node_84

theorem row_node_86 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 12, 2} 4461575 1048832 (by decide) (by decide)]
  decide

theorem row_node_87 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 12, 2} 2364935 1048576 (by decide) (by decide)]
  decide

theorem row_node_88 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {19, 12, 2} 398343 1050624 (by decide) (by decide)]
  decide

theorem row_node_89 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {21, 12, 2} 340999 1048576 (by decide) (by decide)]
  decide

theorem row_node_90 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 12, 2} 8688647 1048576 (by decide) (by decide)]
  decide

theorem row_node_91 :
    (scheme.enumerateGroups [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 2}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_group_cons [16, 17, 18, 19, 20, 21, 22, 23] [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {12, 2} Certificate
  intro e he hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact row_node_86
  · exact row_node_87
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 2} 18) hc)
  · exact row_node_88
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 2} 20) hc)
  · exact row_node_89
  · exact False.elim ((by decide : ¬scheme.Compatible {12, 2} 22) hc)
  · exact row_node_90

theorem row_node_92 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 13, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {16, 13, 2} 4596743 256 (by decide) (by decide)]
  decide

theorem row_node_93 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {17, 13, 2} 2500103 0 (by decide) (by decide)]
  decide

theorem row_node_94 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 13, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {20, 13, 2} 930823 0 (by decide) (by decide)]
  decide

theorem row_node_95 :
    (scheme.enumerateGroups [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 13, 2}).all
      (fun A => decide (Certificate A)) = true := by
  rw [← bits.enumerate_eq [[24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {23, 13, 2} 8823815 0 (by decide) (by decide)]
  decide

end RigidGHZ.Supplement.Periodic.Latin
