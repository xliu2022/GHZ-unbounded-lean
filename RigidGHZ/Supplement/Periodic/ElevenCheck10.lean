module

public import RigidGHZ.Supplement.Periodic.ElevenCheck09

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_320 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 17, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 17, 8} Certificate (by decide)
  decide

theorem node_321 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
    ?_ node_319
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {17, 8} Certificate (by decide)
    ?_ node_320
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 8} Certificate (by decide)
  decide

theorem node_322 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 19, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 19, 8} Certificate (by decide)
  decide

theorem node_323 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 19, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 19, 8} Certificate (by decide)
  decide

theorem node_324 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
    ?_ node_322
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {19, 8} Certificate (by decide)
    ?_ node_323
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 8} Certificate (by decide)
  decide

theorem node_325 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 21, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 21, 8} Certificate (by decide)
  decide

theorem node_326 :
    (scheme.enumerateFrom [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {21, 8} Certificate (by decide)
    ?_ node_325
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {21, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {21, 8} Certificate (by decide)
  decide

theorem node_327 :
    (scheme.enumerateFrom [] {32, 24, 8}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_328 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {24, 8} Certificate (by decide)
    ?_ node_327
  decide

theorem node_329 :
    (scheme.enumerateFrom [] {32, 28, 8}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_330 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 8} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 8} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {28, 8} Certificate (by decide)
    ?_ node_329
  decide

theorem node_331 :
    (scheme.enumerateFrom [] {32, 31, 8}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_332 :
    (scheme.enumerateFrom [32] {31, 8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 32 [] {31, 8} Certificate (by decide)
    ?_ node_331
  decide

theorem node_333 :
    (scheme.enumerateFrom [] {32, 8}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_334 :
    (scheme.enumerateFrom [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_315
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_318
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_321
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_324
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_326
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_328
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {8} Certificate (by decide)
    ?_ node_330
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {8} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {8} Certificate (by decide)
    ?_ node_332
  apply scheme.check_enumeration_split 32 [] {8} Certificate (by decide)
    ?_ node_333
  decide

theorem node_335 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {11, 10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {11, 10, 9} Certificate (by decide)
  decide

theorem node_336 :
    (scheme.enumerateFrom [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
    ?_ node_335
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {10, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {10, 9} Certificate (by decide)
  decide

theorem node_337 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 11, 9} Certificate (by decide)
  decide

theorem node_338 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 11, 9} Certificate (by decide)
  decide

theorem node_339 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 11, 9} Certificate (by decide)
  decide

theorem node_340 :
    (scheme.enumerateFrom [30, 31, 32] {29, 11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 11, 9} Certificate (by decide)
  decide

theorem node_341 :
    (scheme.enumerateFrom [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
    ?_ node_337
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
    ?_ node_338
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
    ?_ node_339
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {11, 9} Certificate (by decide)
    ?_ node_340
  apply scheme.check_enumeration_skip 30 [31, 32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {11, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {11, 9} Certificate (by decide)
  decide

theorem node_342 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14, 13, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14, 13, 9} Certificate (by decide)
  decide

theorem node_343 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
    ?_ node_342
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {14, 13, 9} Certificate (by decide)
  decide

theorem node_344 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 13, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 13, 9} Certificate (by decide)
  decide

theorem node_345 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
    ?_ node_343
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
    ?_ node_344
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 9} Certificate (by decide)
  decide

theorem node_346 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 14, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 14, 9} Certificate (by decide)
  decide

theorem node_347 :
    (scheme.enumerateFrom [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
    ?_ node_346
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {14, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {14, 9} Certificate (by decide)
  decide

theorem node_348 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 9} Certificate (by decide)
  decide

theorem node_349 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 9} Certificate (by decide)
  decide

theorem node_350 :
    (scheme.enumerateFrom [30, 31, 32] {29, 16, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 16, 9} Certificate (by decide)
  decide

theorem node_351 :
    (scheme.enumerateFrom [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
    ?_ node_348
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
    ?_ node_349
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_split 29 [30, 31, 32] {16, 9} Certificate (by decide)
    ?_ node_350
  apply scheme.check_enumeration_skip 30 [31, 32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {16, 9} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {16, 9} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
