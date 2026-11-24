module

public import RigidGHZ.Supplement.Periodic.ElevenCheck10

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_352 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 17, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 17, 9} Certificate (by decide)
  decide

theorem node_353 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 17, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 17, 9} Certificate (by decide)
    ?_ node_352
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 17, 9} Certificate (by decide)
  decide

theorem node_354 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 17, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 17, 9} Certificate (by decide)
  decide

theorem node_355 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
    ?_ node_353
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
    ?_ node_354
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 9} Certificate (by decide)
  decide

theorem node_356 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 19, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 19, 9} Certificate (by decide)
  decide

theorem node_357 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 19, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 19, 9} Certificate (by decide)
    ?_ node_356
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 19, 9} Certificate (by decide)
  decide

theorem node_358 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 19, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 19, 9} Certificate (by decide)
  decide

theorem node_359 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
    ?_ node_357
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
    ?_ node_358
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 9} Certificate (by decide)
  decide

theorem node_360 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 22, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 22, 9} Certificate (by decide)
  decide

theorem node_361 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 22, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 22, 9} Certificate (by decide)
    ?_ node_360
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 22, 9} Certificate (by decide)
  decide

theorem node_362 :
    (scheme.enumerateFrom [30, 31, 32] {29, 22, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 22, 9} Certificate (by decide)
  decide

theorem node_363 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {22, 9} Certificate (by decide)
    ?_ node_361
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {22, 9} Certificate (by decide)
    ?_ node_362
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 9} Certificate (by decide)
  decide

theorem node_364 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25, 9} Certificate (by decide)
  decide

theorem node_365 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25, 9} Certificate (by decide)
    ?_ node_364
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 9} Certificate (by decide)
  decide

theorem node_366 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26, 9} Certificate (by decide)
  decide

theorem node_367 :
    (scheme.enumerateFrom [32] {31, 26, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 26, 9} Certificate (by decide)
  decide

theorem node_368 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26, 9} Certificate (by decide)
    ?_ node_366
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {26, 9} Certificate (by decide)
    ?_ node_367
  apply scheme.check_enumeration_skip 32 [] {26, 9} Certificate (by decide)
  decide

theorem node_369 :
    (scheme.enumerateFrom [30, 31, 32] {29, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 9} Certificate (by decide)
  decide

theorem node_370 :
    (scheme.enumerateFrom [32] {31, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 9} Certificate (by decide)
  decide

theorem node_371 :
    (scheme.enumerateFrom [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_336
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_341
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_345
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_347
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_351
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_355
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_359
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_363
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_365
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {9} Certificate (by decide)
    ?_ node_368
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {9} Certificate (by decide)
    ?_ node_369
  apply scheme.check_enumeration_skip 30 [31, 32] {9} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {9} Certificate (by decide)
    ?_ node_370
  apply scheme.check_enumeration_skip 32 [] {9} Certificate (by decide)
  decide

theorem node_372 :
    (scheme.enumerateFrom [] {32, 11, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_373 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {11, 10} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {11, 10} Certificate (by decide)
    ?_ node_372
  decide

theorem node_374 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 10} Certificate (by decide)
  decide

theorem node_375 :
    (scheme.enumerateFrom [] {32, 20, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_376 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 10} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {20, 10} Certificate (by decide)
    ?_ node_375
  decide

theorem node_377 :
    (scheme.enumerateFrom [] {32, 24, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_378 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 10} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {24, 10} Certificate (by decide)
    ?_ node_377
  decide

theorem node_379 :
    (scheme.enumerateFrom [] {32, 10}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_380 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
    ?_ node_373
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
    ?_ node_374
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
    ?_ node_376
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
    ?_ node_378
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {10} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {10} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {10} Certificate (by decide)
    ?_ node_379
  decide

theorem node_381 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 12, 11} Certificate (by decide)
  decide

theorem node_382 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 12, 11} Certificate (by decide)
  decide

theorem node_383 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 12, 11} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 12, 11} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
