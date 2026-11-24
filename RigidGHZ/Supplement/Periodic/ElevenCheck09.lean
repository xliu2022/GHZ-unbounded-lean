module

public import RigidGHZ.Supplement.Periodic.ElevenCheck08

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_288 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
    ?_ node_287
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 18, 7} Certificate (by decide)
  decide

theorem node_289 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 18, 7} Certificate (by decide)
  decide

theorem node_290 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 18, 7} Certificate (by decide)
    ?_ node_289
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 18, 7} Certificate (by decide)
  decide

theorem node_291 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 18, 7} Certificate (by decide)
  decide

theorem node_292 :
    (scheme.enumerateFrom [30, 31, 32] {29, 18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 18, 7} Certificate (by decide)
  decide

theorem node_293 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
    ?_ node_288
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
    ?_ node_290
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
    ?_ node_291
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {18, 7} Certificate (by decide)
    ?_ node_292
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 7} Certificate (by decide)
  decide

theorem node_294 :
    (scheme.enumerateFrom [31, 32] {30, 25, 19, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 19, 7} Certificate (by decide)
  decide

theorem node_295 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 19, 7} Certificate (by decide)
    ?_ node_294
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 7} Certificate (by decide)
  decide

theorem node_296 :
    (scheme.enumerateFrom [31, 32] {30, 19, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 19, 7} Certificate (by decide)
  decide

theorem node_297 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
    ?_ node_295
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {19, 7} Certificate (by decide)
    ?_ node_296
  apply scheme.check_enumeration_skip 31 [32] {19, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 7} Certificate (by decide)
  decide

theorem node_298 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 21, 7} Certificate (by decide)
  decide

theorem node_299 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 21, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 21, 7} Certificate (by decide)
  decide

theorem node_300 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
    ?_ node_298
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
    ?_ node_299
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 7} Certificate (by decide)
  decide

theorem node_301 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 7} Certificate (by decide)
  decide

theorem node_302 :
    (scheme.enumerateFrom [31, 32] {30, 22, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 22, 7} Certificate (by decide)
  decide

theorem node_303 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 7} Certificate (by decide)
    ?_ node_301
  apply scheme.check_enumeration_split 30 [31, 32] {22, 7} Certificate (by decide)
    ?_ node_302
  apply scheme.check_enumeration_skip 31 [32] {22, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 7} Certificate (by decide)
  decide

theorem node_304 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 25, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 25, 7} Certificate (by decide)
  decide

theorem node_305 :
    (scheme.enumerateFrom [31, 32] {30, 25, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 7} Certificate (by decide)
  decide

theorem node_306 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {25, 7} Certificate (by decide)
    ?_ node_304
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 7} Certificate (by decide)
    ?_ node_305
  apply scheme.check_enumeration_skip 31 [32] {25, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 7} Certificate (by decide)
  decide

theorem node_307 :
    (scheme.enumerateFrom [30, 31, 32] {29, 27, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 27, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 27, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 27, 7} Certificate (by decide)
  decide

theorem node_308 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {27, 7} Certificate (by decide)
    ?_ node_307
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 7} Certificate (by decide)
  decide

theorem node_309 :
    (scheme.enumerateFrom [30, 31, 32] {29, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 7} Certificate (by decide)
  decide

theorem node_310 :
    (scheme.enumerateFrom [31, 32] {30, 7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 7} Certificate (by decide)
  decide

theorem node_311 :
    (scheme.enumerateFrom [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_254
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_265
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_266
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_276
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_280
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_286
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_293
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_297
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_300
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_303
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_306
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {7} Certificate (by decide)
    ?_ node_308
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {7} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {7} Certificate (by decide)
    ?_ node_309
  apply scheme.check_enumeration_split 30 [31, 32] {7} Certificate (by decide)
    ?_ node_310
  apply scheme.check_enumeration_skip 31 [32] {7} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {7} Certificate (by decide)
  decide

theorem node_312 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 9, 8} Certificate (by decide)
  decide

theorem node_313 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 9, 8} Certificate (by decide)
  decide

theorem node_314 :
    (scheme.enumerateFrom [32] {31, 9, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 9, 8} Certificate (by decide)
  decide

theorem node_315 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
    ?_ node_312
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
    ?_ node_313
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {9, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {9, 8} Certificate (by decide)
    ?_ node_314
  apply scheme.check_enumeration_skip 32 [] {9, 8} Certificate (by decide)
  decide

theorem node_316 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 15, 8} Certificate (by decide)
  decide

theorem node_317 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 15, 8} Certificate (by decide)
  decide

theorem node_318 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
    ?_ node_316
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
    ?_ node_317
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 8} Certificate (by decide)
  decide

theorem node_319 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 17, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 17, 8} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
