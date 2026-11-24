module

public import RigidGHZ.Supplement.Periodic.LatinOutput12
public import RigidGHZ.Supplement.Periodic.LatinCatalogueData

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem output_001 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {0} 8388609 256 = [{62, 52, 47, 37, 25, 19, 10, 0}, {60, 54, 47, 32, 29, 17, 11, 0}, {57, 52, 42, 38, 31, 18, 13, 0}, {63, 51, 44, 32, 29, 17, 14, 0}, {57, 52, 47, 37, 26, 18, 14, 0}, {57, 53, 44, 38, 26, 18, 15, 0}, {57, 54, 42, 37, 28, 18, 15, 0}] := by
  have hc0 : ¬(8388609 &&& bits.localMask 8 = 0 ∧ 256 &&& bits.outMask 8 = 0) := by decide
  have hc1 : ¬(8388609 &&& bits.localMask 9 = 0 ∧ 256 &&& bits.outMask 9 = 0) := by decide
  have hc2 : 8388609 &&& bits.localMask 10 = 0 ∧ 256 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 8388609 &&& bits.localMask 11 = 0 ∧ 256 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 8388609 &&& bits.localMask 12 = 0 ∧ 256 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 8388609 &&& bits.localMask 13 = 0 ∧ 256 &&& bits.outMask 13 = 0 := by decide
  have hc6 : 8388609 &&& bits.localMask 14 = 0 ∧ 256 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 8388609 &&& bits.localMask 15 = 0 ∧ 256 &&& bits.outMask 15 = 0 := by decide
  have ha2 : (insert 10 {0} : Finset (Fin 64)) = {10, 0} := by decide
  have hl2 : bits.localMask 10 ||| 8388609 = 8912899 := by decide
  have ho2 : bits.outMask 10 ||| 256 = 1280 := by decide
  have ha3 : (insert 11 {0} : Finset (Fin 64)) = {11, 0} := by decide
  have hl3 : bits.localMask 11 ||| 8388609 = 8652803 := by decide
  have ho3 : bits.outMask 11 ||| 256 = 256 := by decide
  have ha4 : (insert 12 {0} : Finset (Fin 64)) = {12, 0} := by decide
  have hl4 : bits.localMask 12 ||| 8388609 = 8392707 := by decide
  have ho4 : bits.outMask 12 ||| 256 = 1048832 := by decide
  have ha5 : (insert 13 {0} : Finset (Fin 64)) = {13, 0} := by decide
  have hl5 : bits.localMask 13 ||| 8388609 = 8527875 := by decide
  have ho5 : bits.outMask 13 ||| 256 = 256 := by decide
  have ha6 : (insert 14 {0} : Finset (Fin 64)) = {14, 0} := by decide
  have hl6 : bits.localMask 14 ||| 8388609 = 12599299 := by decide
  have ho6 : bits.outMask 14 ||| 256 = 256 := by decide
  have ha7 : (insert 15 {0} : Finset (Fin 64)) = {15, 0} := by decide
  have hl7 : bits.localMask 15 ||| 8388609 = 10518531 := by decide
  have ho7 : bits.outMask 15 ||| 256 = 256 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {0} 8388609 256]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_002, output_003, output_004, output_005, output_006, output_007]
  rfl

theorem output_008 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {1} 66049 0 = [{63, 53, 46, 36, 24, 18, 11, 1}, {60, 54, 43, 32, 29, 23, 11, 1}, {59, 53, 46, 34, 31, 19, 12, 1}, {59, 52, 46, 35, 31, 18, 13, 1}, {59, 52, 42, 39, 27, 22, 13, 1}, {59, 55, 44, 34, 29, 19, 14, 1}, {59, 54, 44, 32, 29, 16, 15, 1}, {56, 53, 46, 36, 26, 18, 15, 1}, {60, 50, 40, 32, 29, 22, 15, 1}] := by
  have hc0 : ¬(66049 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0) := by decide
  have hc1 : ¬(66049 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0) := by decide
  have hc2 : 66049 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 66049 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 66049 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 66049 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0 := by decide
  have hc6 : 66049 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 66049 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0 := by decide
  have ha2 : (insert 10 {1} : Finset (Fin 64)) = {10, 1} := by decide
  have hl2 : bits.localMask 10 ||| 66049 = 590339 := by decide
  have ho2 : bits.outMask 10 ||| 0 = 1024 := by decide
  have ha3 : (insert 11 {1} : Finset (Fin 64)) = {11, 1} := by decide
  have hl3 : bits.localMask 11 ||| 66049 = 330243 := by decide
  have ho3 : bits.outMask 11 ||| 0 = 0 := by decide
  have ha4 : (insert 12 {1} : Finset (Fin 64)) = {12, 1} := by decide
  have hl4 : bits.localMask 12 ||| 66049 = 70147 := by decide
  have ho4 : bits.outMask 12 ||| 0 = 1048576 := by decide
  have ha5 : (insert 13 {1} : Finset (Fin 64)) = {13, 1} := by decide
  have hl5 : bits.localMask 13 ||| 66049 = 205315 := by decide
  have ho5 : bits.outMask 13 ||| 0 = 0 := by decide
  have ha6 : (insert 14 {1} : Finset (Fin 64)) = {14, 1} := by decide
  have hl6 : bits.localMask 14 ||| 66049 = 4276739 := by decide
  have ho6 : bits.outMask 14 ||| 0 = 0 := by decide
  have ha7 : (insert 15 {1} : Finset (Fin 64)) = {15, 1} := by decide
  have hl7 : bits.localMask 15 ||| 66049 = 2195971 := by decide
  have ho7 : bits.outMask 15 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {1} 66049 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_009, output_010, output_011, output_012, output_013, output_014]
  rfl

theorem output_015 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {2} 263169 0 = [{60, 54, 45, 39, 27, 17, 8, 2}, {63, 53, 41, 34, 30, 20, 8, 2}, {63, 52, 41, 35, 30, 21, 10, 2}, {62, 53, 43, 33, 28, 23, 10, 2}, {61, 54, 41, 35, 28, 23, 10, 2}, {57, 53, 47, 34, 30, 19, 12, 2}, {57, 53, 43, 38, 26, 23, 12, 2}, {59, 53, 41, 38, 26, 20, 15, 2}] := by
  have hc0 : 263169 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 263169 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0 := by decide
  have hc2 : 263169 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0 := by decide
  have hc3 : ¬(263169 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0) := by decide
  have hc4 : 263169 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 263169 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0 := by decide
  have hc6 : 263169 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 263169 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0 := by decide
  have ha0 : (insert 8 {2} : Finset (Fin 64)) = {8, 2} := by decide
  have hl0 : bits.localMask 8 ||| 263169 = 328707 := by decide
  have ho0 : bits.outMask 8 ||| 0 = 256 := by decide
  have ha1 : (insert 9 {2} : Finset (Fin 64)) = {9, 2} := by decide
  have hl1 : bits.localMask 9 ||| 263169 = 8652291 := by decide
  have ho1 : bits.outMask 9 ||| 0 = 0 := by decide
  have ha2 : (insert 10 {2} : Finset (Fin 64)) = {10, 2} := by decide
  have hl2 : bits.localMask 10 ||| 263169 = 787459 := by decide
  have ho2 : bits.outMask 10 ||| 0 = 1024 := by decide
  have ha4 : (insert 12 {2} : Finset (Fin 64)) = {12, 2} := by decide
  have hl4 : bits.localMask 12 ||| 263169 = 267267 := by decide
  have ho4 : bits.outMask 12 ||| 0 = 1048576 := by decide
  have ha5 : (insert 13 {2} : Finset (Fin 64)) = {13, 2} := by decide
  have hl5 : bits.localMask 13 ||| 263169 = 402435 := by decide
  have ho5 : bits.outMask 13 ||| 0 = 0 := by decide
  have ha6 : (insert 14 {2} : Finset (Fin 64)) = {14, 2} := by decide
  have hl6 : bits.localMask 14 ||| 263169 = 4473859 := by decide
  have ho6 : bits.outMask 14 ||| 0 = 0 := by decide
  have ha7 : (insert 15 {2} : Finset (Fin 64)) = {15, 2} := by decide
  have hl7 : bits.localMask 15 ||| 263169 = 2393091 := by decide
  have ho7 : bits.outMask 15 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {2} 263169 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha4, hl4, ho4, ha5, hl5, ho5, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_016, output_017, output_018, output_019, output_020, output_021, output_022]
  rfl

theorem output_023 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {3} 1048577 2048 = [{63, 53, 44, 32, 30, 17, 8, 3}, {60, 54, 45, 32, 31, 17, 8, 3}, {63, 52, 45, 32, 25, 22, 8, 3}, {61, 54, 44, 32, 25, 23, 8, 3}, {61, 55, 44, 38, 26, 16, 9, 3}, {60, 55, 45, 38, 26, 17, 11, 3}, {59, 52, 47, 32, 25, 22, 13, 3}, {59, 55, 40, 37, 28, 17, 14, 3}, {59, 55, 44, 33, 24, 21, 14, 3}, {61, 49, 40, 32, 28, 23, 14, 3}, {59, 54, 44, 32, 25, 21, 15, 3}, {60, 49, 40, 32, 30, 21, 15, 3}] := by
  have hc0 : 1048577 &&& bits.localMask 8 = 0 ∧ 2048 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 1048577 &&& bits.localMask 9 = 0 ∧ 2048 &&& bits.outMask 9 = 0 := by decide
  have hc2 : 1048577 &&& bits.localMask 10 = 0 ∧ 2048 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 1048577 &&& bits.localMask 11 = 0 ∧ 2048 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 1048577 &&& bits.localMask 12 = 0 ∧ 2048 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 1048577 &&& bits.localMask 13 = 0 ∧ 2048 &&& bits.outMask 13 = 0 := by decide
  have hc6 : 1048577 &&& bits.localMask 14 = 0 ∧ 2048 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 1048577 &&& bits.localMask 15 = 0 ∧ 2048 &&& bits.outMask 15 = 0 := by decide
  have ha0 : (insert 8 {3} : Finset (Fin 64)) = {8, 3} := by decide
  have hl0 : bits.localMask 8 ||| 1048577 = 1114115 := by decide
  have ho0 : bits.outMask 8 ||| 2048 = 2304 := by decide
  have ha1 : (insert 9 {3} : Finset (Fin 64)) = {9, 3} := by decide
  have hl1 : bits.localMask 9 ||| 1048577 = 9437699 := by decide
  have ho1 : bits.outMask 9 ||| 2048 = 2048 := by decide
  have ha2 : (insert 10 {3} : Finset (Fin 64)) = {10, 3} := by decide
  have hl2 : bits.localMask 10 ||| 1048577 = 1572867 := by decide
  have ho2 : bits.outMask 10 ||| 2048 = 3072 := by decide
  have ha3 : (insert 11 {3} : Finset (Fin 64)) = {11, 3} := by decide
  have hl3 : bits.localMask 11 ||| 1048577 = 1312771 := by decide
  have ho3 : bits.outMask 11 ||| 2048 = 2048 := by decide
  have ha4 : (insert 12 {3} : Finset (Fin 64)) = {12, 3} := by decide
  have hl4 : bits.localMask 12 ||| 1048577 = 1052675 := by decide
  have ho4 : bits.outMask 12 ||| 2048 = 1050624 := by decide
  have ha5 : (insert 13 {3} : Finset (Fin 64)) = {13, 3} := by decide
  have hl5 : bits.localMask 13 ||| 1048577 = 1187843 := by decide
  have ho5 : bits.outMask 13 ||| 2048 = 2048 := by decide
  have ha6 : (insert 14 {3} : Finset (Fin 64)) = {14, 3} := by decide
  have hl6 : bits.localMask 14 ||| 1048577 = 5259267 := by decide
  have ho6 : bits.outMask 14 ||| 2048 = 2048 := by decide
  have ha7 : (insert 15 {3} : Finset (Fin 64)) = {15, 3} := by decide
  have hl7 : bits.localMask 15 ||| 1048577 = 3178499 := by decide
  have ho7 : bits.outMask 15 ||| 2048 = 2048 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {3} 1048577 2048]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_024, output_025, output_026, output_027, output_028, output_029, output_030, output_031]
  rfl

theorem output_032 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {4} 135169 0 = [{61, 51, 46, 35, 31, 18, 9, 4}, {61, 51, 42, 39, 27, 22, 9, 4}, {61, 50, 41, 38, 31, 16, 10, 4}, {62, 51, 45, 35, 31, 17, 10, 4}, {61, 49, 47, 35, 30, 18, 10, 4}, {62, 51, 43, 37, 25, 23, 10, 4}, {57, 53, 47, 34, 30, 18, 11, 4}, {59, 48, 47, 37, 27, 17, 14, 4}, {56, 51, 45, 39, 27, 17, 14, 4}, {56, 50, 47, 32, 29, 17, 14, 4}, {57, 51, 45, 34, 31, 18, 14, 4}, {58, 49, 43, 32, 29, 23, 14, 4}, {57, 51, 42, 37, 30, 18, 15, 4}] := by
  have hc0 : 135169 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 135169 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0 := by decide
  have hc2 : 135169 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 135169 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0 := by decide
  have hc4 : ¬(135169 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0) := by decide
  have hc5 : ¬(135169 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0) := by decide
  have hc6 : 135169 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 135169 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0 := by decide
  have ha0 : (insert 8 {4} : Finset (Fin 64)) = {8, 4} := by decide
  have hl0 : bits.localMask 8 ||| 135169 = 200707 := by decide
  have ho0 : bits.outMask 8 ||| 0 = 256 := by decide
  have ha1 : (insert 9 {4} : Finset (Fin 64)) = {9, 4} := by decide
  have hl1 : bits.localMask 9 ||| 135169 = 8524291 := by decide
  have ho1 : bits.outMask 9 ||| 0 = 0 := by decide
  have ha2 : (insert 10 {4} : Finset (Fin 64)) = {10, 4} := by decide
  have hl2 : bits.localMask 10 ||| 135169 = 659459 := by decide
  have ho2 : bits.outMask 10 ||| 0 = 1024 := by decide
  have ha3 : (insert 11 {4} : Finset (Fin 64)) = {11, 4} := by decide
  have hl3 : bits.localMask 11 ||| 135169 = 399363 := by decide
  have ho3 : bits.outMask 11 ||| 0 = 0 := by decide
  have ha6 : (insert 14 {4} : Finset (Fin 64)) = {14, 4} := by decide
  have hl6 : bits.localMask 14 ||| 135169 = 4345859 := by decide
  have ho6 : bits.outMask 14 ||| 0 = 0 := by decide
  have ha7 : (insert 15 {4} : Finset (Fin 64)) = {15, 4} := by decide
  have hl7 : bits.localMask 15 ||| 135169 = 2265091 := by decide
  have ho7 : bits.outMask 15 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {4} 135169 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha3, hl3, ho3, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_033, output_034, output_035, output_036, output_037, output_038]
  rfl

theorem output_039 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {5} 532481 0 = [{63, 48, 44, 35, 30, 17, 8, 5}, {63, 48, 43, 36, 25, 22, 8, 5}, {60, 51, 43, 39, 26, 22, 9, 5}, {56, 48, 47, 36, 26, 17, 14, 5}, {58, 48, 40, 36, 31, 17, 14, 5}, {58, 48, 44, 33, 24, 23, 14, 5}, {56, 48, 43, 33, 28, 23, 14, 5}, {58, 48, 44, 33, 30, 16, 15, 5}, {59, 48, 44, 38, 25, 19, 15, 5}, {58, 48, 40, 36, 25, 22, 15, 5}, {59, 48, 42, 33, 28, 22, 15, 5}] := by
  have hc0 : 532481 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 532481 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0 := by decide
  have hc2 : ¬(532481 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0) := by decide
  have hc3 : 532481 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 532481 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0 := by decide
  have hc5 : ¬(532481 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0) := by decide
  have hc6 : 532481 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0 := by decide
  have hc7 : 532481 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0 := by decide
  have ha0 : (insert 8 {5} : Finset (Fin 64)) = {8, 5} := by decide
  have hl0 : bits.localMask 8 ||| 532481 = 598019 := by decide
  have ho0 : bits.outMask 8 ||| 0 = 256 := by decide
  have ha1 : (insert 9 {5} : Finset (Fin 64)) = {9, 5} := by decide
  have hl1 : bits.localMask 9 ||| 532481 = 8921603 := by decide
  have ho1 : bits.outMask 9 ||| 0 = 0 := by decide
  have ha3 : (insert 11 {5} : Finset (Fin 64)) = {11, 5} := by decide
  have hl3 : bits.localMask 11 ||| 532481 = 796675 := by decide
  have ho3 : bits.outMask 11 ||| 0 = 0 := by decide
  have ha4 : (insert 12 {5} : Finset (Fin 64)) = {12, 5} := by decide
  have hl4 : bits.localMask 12 ||| 532481 = 536579 := by decide
  have ho4 : bits.outMask 12 ||| 0 = 1048576 := by decide
  have ha6 : (insert 14 {5} : Finset (Fin 64)) = {14, 5} := by decide
  have hl6 : bits.localMask 14 ||| 532481 = 4743171 := by decide
  have ho6 : bits.outMask 14 ||| 0 = 0 := by decide
  have ha7 : (insert 15 {5} : Finset (Fin 64)) = {15, 5} := by decide
  have hl7 : bits.localMask 15 ||| 532481 = 2662403 := by decide
  have ho7 : bits.outMask 15 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {5} 532481 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha3, hl3, ho3, ha4, hl4, ho4, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_040, output_041, output_042, output_043, output_044, output_045]
  rfl

theorem output_046 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {6} 2113537 0 = [{63, 51, 44, 32, 29, 16, 9, 6}, {63, 50, 41, 37, 28, 16, 10, 6}, {63, 49, 45, 35, 28, 18, 10, 6}, {60, 51, 45, 33, 31, 18, 10, 6}, {58, 53, 41, 36, 31, 19, 10, 6}, {57, 53, 47, 36, 26, 18, 11, 6}, {57, 50, 47, 37, 26, 16, 12, 6}, {57, 50, 40, 35, 31, 21, 12, 6}, {57, 51, 42, 36, 31, 18, 13, 6}] := by
  have hc0 : 2113537 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 2113537 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0 := by decide
  have hc2 : 2113537 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 2113537 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 2113537 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 2113537 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0 := by decide
  have hc6 : ¬(2113537 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0) := by decide
  have hc7 : ¬(2113537 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0) := by decide
  have ha0 : (insert 8 {6} : Finset (Fin 64)) = {8, 6} := by decide
  have hl0 : bits.localMask 8 ||| 2113537 = 2179075 := by decide
  have ho0 : bits.outMask 8 ||| 0 = 256 := by decide
  have ha1 : (insert 9 {6} : Finset (Fin 64)) = {9, 6} := by decide
  have hl1 : bits.localMask 9 ||| 2113537 = 10502659 := by decide
  have ho1 : bits.outMask 9 ||| 0 = 0 := by decide
  have ha2 : (insert 10 {6} : Finset (Fin 64)) = {10, 6} := by decide
  have hl2 : bits.localMask 10 ||| 2113537 = 2637827 := by decide
  have ho2 : bits.outMask 10 ||| 0 = 1024 := by decide
  have ha3 : (insert 11 {6} : Finset (Fin 64)) = {11, 6} := by decide
  have hl3 : bits.localMask 11 ||| 2113537 = 2377731 := by decide
  have ho3 : bits.outMask 11 ||| 0 = 0 := by decide
  have ha4 : (insert 12 {6} : Finset (Fin 64)) = {12, 6} := by decide
  have hl4 : bits.localMask 12 ||| 2113537 = 2117635 := by decide
  have ho4 : bits.outMask 12 ||| 0 = 1048576 := by decide
  have ha5 : (insert 13 {6} : Finset (Fin 64)) = {13, 6} := by decide
  have hl5 : bits.localMask 13 ||| 2113537 = 2252803 := by decide
  have ho5 : bits.outMask 13 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {6} 2113537 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5]
  rw [output_047, output_048, output_049, output_050, output_051, output_052]
  rfl

theorem output_053 : bits.enumerate [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {7} 4227073 0 = [{59, 54, 44, 32, 29, 17, 8, 7}, {61, 49, 46, 36, 26, 18, 8, 7}, {62, 51, 43, 37, 26, 20, 9, 7}, {58, 52, 40, 32, 29, 22, 9, 7}, {62, 50, 40, 37, 28, 17, 10, 7}, {61, 51, 44, 33, 30, 18, 10, 7}, {58, 52, 41, 37, 30, 19, 10, 7}, {62, 50, 44, 33, 24, 21, 10, 7}, {57, 52, 45, 38, 26, 18, 11, 7}, {57, 54, 45, 34, 28, 18, 11, 7}, {61, 50, 41, 38, 26, 20, 11, 7}, {59, 48, 44, 38, 27, 17, 13, 7}, {59, 49, 46, 34, 28, 18, 13, 7}, {57, 51, 44, 34, 30, 18, 13, 7}, {56, 51, 41, 34, 30, 20, 13, 7}] := by
  have hc0 : 4227073 &&& bits.localMask 8 = 0 ∧ 0 &&& bits.outMask 8 = 0 := by decide
  have hc1 : 4227073 &&& bits.localMask 9 = 0 ∧ 0 &&& bits.outMask 9 = 0 := by decide
  have hc2 : 4227073 &&& bits.localMask 10 = 0 ∧ 0 &&& bits.outMask 10 = 0 := by decide
  have hc3 : 4227073 &&& bits.localMask 11 = 0 ∧ 0 &&& bits.outMask 11 = 0 := by decide
  have hc4 : 4227073 &&& bits.localMask 12 = 0 ∧ 0 &&& bits.outMask 12 = 0 := by decide
  have hc5 : 4227073 &&& bits.localMask 13 = 0 ∧ 0 &&& bits.outMask 13 = 0 := by decide
  have hc6 : ¬(4227073 &&& bits.localMask 14 = 0 ∧ 0 &&& bits.outMask 14 = 0) := by decide
  have hc7 : ¬(4227073 &&& bits.localMask 15 = 0 ∧ 0 &&& bits.outMask 15 = 0) := by decide
  have ha0 : (insert 8 {7} : Finset (Fin 64)) = {8, 7} := by decide
  have hl0 : bits.localMask 8 ||| 4227073 = 4292611 := by decide
  have ho0 : bits.outMask 8 ||| 0 = 256 := by decide
  have ha1 : (insert 9 {7} : Finset (Fin 64)) = {9, 7} := by decide
  have hl1 : bits.localMask 9 ||| 4227073 = 12616195 := by decide
  have ho1 : bits.outMask 9 ||| 0 = 0 := by decide
  have ha2 : (insert 10 {7} : Finset (Fin 64)) = {10, 7} := by decide
  have hl2 : bits.localMask 10 ||| 4227073 = 4751363 := by decide
  have ho2 : bits.outMask 10 ||| 0 = 1024 := by decide
  have ha3 : (insert 11 {7} : Finset (Fin 64)) = {11, 7} := by decide
  have hl3 : bits.localMask 11 ||| 4227073 = 4491267 := by decide
  have ho3 : bits.outMask 11 ||| 0 = 0 := by decide
  have ha4 : (insert 12 {7} : Finset (Fin 64)) = {12, 7} := by decide
  have hl4 : bits.localMask 12 ||| 4227073 = 4231171 := by decide
  have ho4 : bits.outMask 12 ||| 0 = 1048576 := by decide
  have ha5 : (insert 13 {7} : Finset (Fin 64)) = {13, 7} := by decide
  have hl5 : bits.localMask 13 ||| 4227073 = 4366339 := by decide
  have ho5 : bits.outMask 13 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [8, 9, 10, 11, 12, 13, 14, 15] [[16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] {7} 4227073 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5]
  rw [output_054, output_055, output_056, output_057, output_058, output_059]
  rfl

theorem output_000 : bits.enumerate [[0, 1, 2, 3, 4, 5, 6, 7], [8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] ∅ 0 0 = [{62, 52, 47, 37, 25, 19, 10, 0}, {60, 54, 47, 32, 29, 17, 11, 0}, {57, 52, 42, 38, 31, 18, 13, 0}, {63, 51, 44, 32, 29, 17, 14, 0}, {57, 52, 47, 37, 26, 18, 14, 0}, {57, 53, 44, 38, 26, 18, 15, 0}, {57, 54, 42, 37, 28, 18, 15, 0}, {63, 53, 46, 36, 24, 18, 11, 1}, {60, 54, 43, 32, 29, 23, 11, 1}, {59, 53, 46, 34, 31, 19, 12, 1}, {59, 52, 46, 35, 31, 18, 13, 1}, {59, 52, 42, 39, 27, 22, 13, 1}, {59, 55, 44, 34, 29, 19, 14, 1}, {59, 54, 44, 32, 29, 16, 15, 1}, {56, 53, 46, 36, 26, 18, 15, 1}, {60, 50, 40, 32, 29, 22, 15, 1}, {60, 54, 45, 39, 27, 17, 8, 2}, {63, 53, 41, 34, 30, 20, 8, 2}, {63, 52, 41, 35, 30, 21, 10, 2}, {62, 53, 43, 33, 28, 23, 10, 2}, {61, 54, 41, 35, 28, 23, 10, 2}, {57, 53, 47, 34, 30, 19, 12, 2}, {57, 53, 43, 38, 26, 23, 12, 2}, {59, 53, 41, 38, 26, 20, 15, 2}, {63, 53, 44, 32, 30, 17, 8, 3}, {60, 54, 45, 32, 31, 17, 8, 3}, {63, 52, 45, 32, 25, 22, 8, 3}, {61, 54, 44, 32, 25, 23, 8, 3}, {61, 55, 44, 38, 26, 16, 9, 3}, {60, 55, 45, 38, 26, 17, 11, 3}, {59, 52, 47, 32, 25, 22, 13, 3}, {59, 55, 40, 37, 28, 17, 14, 3}, {59, 55, 44, 33, 24, 21, 14, 3}, {61, 49, 40, 32, 28, 23, 14, 3}, {59, 54, 44, 32, 25, 21, 15, 3}, {60, 49, 40, 32, 30, 21, 15, 3}, {61, 51, 46, 35, 31, 18, 9, 4}, {61, 51, 42, 39, 27, 22, 9, 4}, {61, 50, 41, 38, 31, 16, 10, 4}, {62, 51, 45, 35, 31, 17, 10, 4}, {61, 49, 47, 35, 30, 18, 10, 4}, {62, 51, 43, 37, 25, 23, 10, 4}, {57, 53, 47, 34, 30, 18, 11, 4}, {59, 48, 47, 37, 27, 17, 14, 4}, {56, 51, 45, 39, 27, 17, 14, 4}, {56, 50, 47, 32, 29, 17, 14, 4}, {57, 51, 45, 34, 31, 18, 14, 4}, {58, 49, 43, 32, 29, 23, 14, 4}, {57, 51, 42, 37, 30, 18, 15, 4}, {63, 48, 44, 35, 30, 17, 8, 5}, {63, 48, 43, 36, 25, 22, 8, 5}, {60, 51, 43, 39, 26, 22, 9, 5}, {56, 48, 47, 36, 26, 17, 14, 5}, {58, 48, 40, 36, 31, 17, 14, 5}, {58, 48, 44, 33, 24, 23, 14, 5}, {56, 48, 43, 33, 28, 23, 14, 5}, {58, 48, 44, 33, 30, 16, 15, 5}, {59, 48, 44, 38, 25, 19, 15, 5}, {58, 48, 40, 36, 25, 22, 15, 5}, {59, 48, 42, 33, 28, 22, 15, 5}, {63, 51, 44, 32, 29, 16, 9, 6}, {63, 50, 41, 37, 28, 16, 10, 6}, {63, 49, 45, 35, 28, 18, 10, 6}, {60, 51, 45, 33, 31, 18, 10, 6}, {58, 53, 41, 36, 31, 19, 10, 6}, {57, 53, 47, 36, 26, 18, 11, 6}, {57, 50, 47, 37, 26, 16, 12, 6}, {57, 50, 40, 35, 31, 21, 12, 6}, {57, 51, 42, 36, 31, 18, 13, 6}, {59, 54, 44, 32, 29, 17, 8, 7}, {61, 49, 46, 36, 26, 18, 8, 7}, {62, 51, 43, 37, 26, 20, 9, 7}, {58, 52, 40, 32, 29, 22, 9, 7}, {62, 50, 40, 37, 28, 17, 10, 7}, {61, 51, 44, 33, 30, 18, 10, 7}, {58, 52, 41, 37, 30, 19, 10, 7}, {62, 50, 44, 33, 24, 21, 10, 7}, {57, 52, 45, 38, 26, 18, 11, 7}, {57, 54, 45, 34, 28, 18, 11, 7}, {61, 50, 41, 38, 26, 20, 11, 7}, {59, 48, 44, 38, 27, 17, 13, 7}, {59, 49, 46, 34, 28, 18, 13, 7}, {57, 51, 44, 34, 30, 18, 13, 7}, {56, 51, 41, 34, 30, 20, 13, 7}] := by
  have hc0 : 0 &&& bits.localMask 0 = 0 ∧ 0 &&& bits.outMask 0 = 0 := by decide
  have hc1 : 0 &&& bits.localMask 1 = 0 ∧ 0 &&& bits.outMask 1 = 0 := by decide
  have hc2 : 0 &&& bits.localMask 2 = 0 ∧ 0 &&& bits.outMask 2 = 0 := by decide
  have hc3 : 0 &&& bits.localMask 3 = 0 ∧ 0 &&& bits.outMask 3 = 0 := by decide
  have hc4 : 0 &&& bits.localMask 4 = 0 ∧ 0 &&& bits.outMask 4 = 0 := by decide
  have hc5 : 0 &&& bits.localMask 5 = 0 ∧ 0 &&& bits.outMask 5 = 0 := by decide
  have hc6 : 0 &&& bits.localMask 6 = 0 ∧ 0 &&& bits.outMask 6 = 0 := by decide
  have hc7 : 0 &&& bits.localMask 7 = 0 ∧ 0 &&& bits.outMask 7 = 0 := by decide
  have ha0 : (insert 0 ∅ : Finset (Fin 64)) = {0} := by decide
  have hl0 : bits.localMask 0 ||| 0 = 8388609 := by decide
  have ho0 : bits.outMask 0 ||| 0 = 256 := by decide
  have ha1 : (insert 1 ∅ : Finset (Fin 64)) = {1} := by decide
  have hl1 : bits.localMask 1 ||| 0 = 66049 := by decide
  have ho1 : bits.outMask 1 ||| 0 = 0 := by decide
  have ha2 : (insert 2 ∅ : Finset (Fin 64)) = {2} := by decide
  have hl2 : bits.localMask 2 ||| 0 = 263169 := by decide
  have ho2 : bits.outMask 2 ||| 0 = 0 := by decide
  have ha3 : (insert 3 ∅ : Finset (Fin 64)) = {3} := by decide
  have hl3 : bits.localMask 3 ||| 0 = 1048577 := by decide
  have ho3 : bits.outMask 3 ||| 0 = 2048 := by decide
  have ha4 : (insert 4 ∅ : Finset (Fin 64)) = {4} := by decide
  have hl4 : bits.localMask 4 ||| 0 = 135169 := by decide
  have ho4 : bits.outMask 4 ||| 0 = 0 := by decide
  have ha5 : (insert 5 ∅ : Finset (Fin 64)) = {5} := by decide
  have hl5 : bits.localMask 5 ||| 0 = 532481 := by decide
  have ho5 : bits.outMask 5 ||| 0 = 0 := by decide
  have ha6 : (insert 6 ∅ : Finset (Fin 64)) = {6} := by decide
  have hl6 : bits.localMask 6 ||| 0 = 2113537 := by decide
  have ho6 : bits.outMask 6 ||| 0 = 0 := by decide
  have ha7 : (insert 7 ∅ : Finset (Fin 64)) = {7} := by decide
  have hl7 : bits.localMask 7 ||| 0 = 4227073 := by decide
  have ho7 : bits.outMask 7 ||| 0 = 0 := by decide
  rw [bits.enumerate_cons [0, 1, 2, 3, 4, 5, 6, 7] [[8, 9, 10, 11, 12, 13, 14, 15], [16, 17, 18, 19, 20, 21, 22, 23], [24, 25, 26, 27, 28, 29, 30, 31], [32, 33, 34, 35, 36, 37, 38, 39], [40, 41, 42, 43, 44, 45, 46, 47], [48, 49, 50, 51, 52, 53, 54, 55], [56, 57, 58, 59, 60, 61, 62, 63]] ∅ 0 0]
  simp only [List.flatMap_cons, List.flatMap_nil, hc0, hc1, hc2, hc3, hc4, hc5, hc6, hc7, ite_eq_left, ite_eq_right, List.append_nil, List.nil_append]
  simp only [ha0, hl0, ho0, ha1, hl1, ho1, ha2, hl2, ho2, ha3, hl3, ho3, ha4, hl4, ho4, ha5, hl5, ho5, ha6, hl6, ho6, ha7, hl7, ho7]
  rw [output_001, output_008, output_015, output_023, output_032, output_039, output_046, output_053]
  rfl

theorem enumeration_eq_list : bits.enumerate groups ∅ 0 0 = catalogueList := by
  exact output_000

end RigidGHZ.Supplement.Periodic.Latin
