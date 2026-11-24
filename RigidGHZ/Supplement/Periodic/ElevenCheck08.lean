module

public import RigidGHZ.Supplement.Periodic.ElevenCheck07

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_256 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 9, 7} Certificate (by decide)
  decide

theorem node_257 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 9, 7} Certificate (by decide)
  decide

theorem node_258 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
    ?_ node_257
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 9, 7} Certificate (by decide)
  decide

theorem node_259 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 9, 7} Certificate (by decide)
  decide

theorem node_260 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
    ?_ node_259
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 9, 7} Certificate (by decide)
  decide

theorem node_261 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 9, 7} Certificate (by decide)
  decide

theorem node_262 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 9, 7} Certificate (by decide)
    ?_ node_261
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 9, 7} Certificate (by decide)
  decide

theorem node_263 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 9, 7} Certificate (by decide)
  decide

theorem node_264 :
    (scheme.enumerateFrom [30, 31, 32] {29, 9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 9, 7} Certificate (by decide)
  decide

theorem node_265 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_255
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_256
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_258
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_260
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_262
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_263
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {9, 7} Certificate (by decide)
    ?_ node_264
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {9, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {9, 7} Certificate (by decide)
  decide

theorem node_266 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {10, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {10, 7} Certificate (by decide)
  decide

theorem node_267 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 12, 7} Certificate (by decide)
  decide

theorem node_268 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 12, 7} Certificate (by decide)
  decide

theorem node_269 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
    ?_ node_268
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 12, 7} Certificate (by decide)
  decide

theorem node_270 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 12, 7} Certificate (by decide)
  decide

theorem node_271 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
    ?_ node_270
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 12, 7} Certificate (by decide)
  decide

theorem node_272 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 12, 7} Certificate (by decide)
  decide

theorem node_273 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 12, 7} Certificate (by decide)
    ?_ node_272
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 12, 7} Certificate (by decide)
  decide

theorem node_274 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 12, 7} Certificate (by decide)
  decide

theorem node_275 :
    (scheme.enumerateFrom [30, 31, 32] {29, 12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 12, 7} Certificate (by decide)
  decide

theorem node_276 :
    (scheme.enumerateFrom [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_267
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_269
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_271
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_273
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_274
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {12, 7} Certificate (by decide)
    ?_ node_275
  apply scheme.check_enumeration_skip 30 [31, 32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {12, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {12, 7} Certificate (by decide)
  decide

theorem node_277 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 13, 7} Certificate (by decide)
  decide

theorem node_278 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 13, 7} Certificate (by decide)
  decide

theorem node_279 :
    (scheme.enumerateFrom [31, 32] {30, 13, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 13, 7} Certificate (by decide)
  decide

theorem node_280 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
    ?_ node_277
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
    ?_ node_278
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {13, 7} Certificate (by decide)
    ?_ node_279
  apply scheme.check_enumeration_skip 31 [32] {13, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 7} Certificate (by decide)
  decide

theorem node_281 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 18, 17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 18, 17, 7} Certificate (by decide)
  decide

theorem node_282 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
    ?_ node_281
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 17, 7} Certificate (by decide)
  decide

theorem node_283 :
    (scheme.enumerateFrom [31, 32] {30, 25, 17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 17, 7} Certificate (by decide)
  decide

theorem node_284 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 17, 7} Certificate (by decide)
    ?_ node_283
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 7} Certificate (by decide)
  decide

theorem node_285 :
    (scheme.enumerateFrom [31, 32] {30, 17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 17, 7} Certificate (by decide)
  decide

theorem node_286 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
    ?_ node_282
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
    ?_ node_284
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {17, 7} Certificate (by decide)
    ?_ node_285
  apply scheme.check_enumeration_skip 31 [32] {17, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 7} Certificate (by decide)
  decide

theorem node_287 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 18, 7} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
