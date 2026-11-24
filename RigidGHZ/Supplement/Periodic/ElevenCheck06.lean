module

public import RigidGHZ.Supplement.Periodic.ElevenCheck05

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_192 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 15, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 15, 4} Certificate (by decide)
  decide

theorem node_193 :
    (scheme.enumerateFrom [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
    ?_ node_191
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
    ?_ node_192
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {15, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {15, 4} Certificate (by decide)
  decide

theorem node_194 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {20, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 18, 4} Certificate (by decide)
  decide

theorem node_195 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {22, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 18, 4} Certificate (by decide)
  decide

theorem node_196 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 18, 4} Certificate (by decide)
  decide

theorem node_197 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 18, 4} Certificate (by decide)
  decide

theorem node_198 :
    (scheme.enumerateFrom [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
    ?_ node_194
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
    ?_ node_195
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
    ?_ node_196
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {18, 4} Certificate (by decide)
    ?_ node_197
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {18, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {18, 4} Certificate (by decide)
  decide

theorem node_199 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 20, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 20, 4} Certificate (by decide)
  decide

theorem node_200 :
    (scheme.enumerateFrom [31, 32] {30, 20, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 20, 4} Certificate (by decide)
  decide

theorem node_201 :
    (scheme.enumerateFrom [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {20, 4} Certificate (by decide)
    ?_ node_199
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {20, 4} Certificate (by decide)
    ?_ node_200
  apply scheme.check_enumeration_skip 31 [32] {20, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {20, 4} Certificate (by decide)
  decide

theorem node_202 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 22, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 22, 4} Certificate (by decide)
  decide

theorem node_203 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 22, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 22, 4} Certificate (by decide)
  decide

theorem node_204 :
    (scheme.enumerateFrom [31, 32] {30, 22, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 22, 4} Certificate (by decide)
  decide

theorem node_205 :
    (scheme.enumerateFrom [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {22, 4} Certificate (by decide)
    ?_ node_202
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {22, 4} Certificate (by decide)
    ?_ node_203
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {22, 4} Certificate (by decide)
    ?_ node_204
  apply scheme.check_enumeration_skip 31 [32] {22, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {22, 4} Certificate (by decide)
  decide

theorem node_206 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 23, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 23, 4} Certificate (by decide)
  decide

theorem node_207 :
    (scheme.enumerateFrom [24, 25, 26, 27, 28, 29, 30, 31, 32] {23, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {23, 4} Certificate (by decide)
    ?_ node_206
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {23, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {23, 4} Certificate (by decide)
  decide

theorem node_208 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 24, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {25, 24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 24, 4} Certificate (by decide)
  decide

theorem node_209 :
    (scheme.enumerateFrom [25, 26, 27, 28, 29, 30, 31, 32] {24, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {24, 4} Certificate (by decide)
    ?_ node_208
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {24, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {24, 4} Certificate (by decide)
  decide

theorem node_210 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 25, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 25, 4} Certificate (by decide)
  decide

theorem node_211 :
    (scheme.enumerateFrom [31, 32] {30, 25, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 25, 4} Certificate (by decide)
  decide

theorem node_212 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {25, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {25, 4} Certificate (by decide)
    ?_ node_210
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25, 4} Certificate (by decide)
    ?_ node_211
  apply scheme.check_enumeration_skip 31 [32] {25, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {25, 4} Certificate (by decide)
  decide

theorem node_213 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 27, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 27, 4} Certificate (by decide)
  decide

theorem node_214 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {27, 4} Certificate (by decide)
    ?_ node_213
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 4} Certificate (by decide)
  decide

theorem node_215 :
    (scheme.enumerateFrom [31, 32] {30, 28, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 28, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 28, 4} Certificate (by decide)
  decide

theorem node_216 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {28, 4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {28, 4} Certificate (by decide)
    ?_ node_215
  apply scheme.check_enumeration_skip 31 [32] {28, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 4} Certificate (by decide)
  decide

theorem node_217 :
    (scheme.enumerateFrom [31, 32] {30, 4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {30, 4} Certificate (by decide)
  decide

theorem node_218 :
    (scheme.enumerateFrom [5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 5 [6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_168
  apply scheme.check_enumeration_skip 6 [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_173
  apply scheme.check_enumeration_split 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_177
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_181
  apply scheme.check_enumeration_split 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_190
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_193
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_198
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_201
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_205
  apply scheme.check_enumeration_split 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_207
  apply scheme.check_enumeration_split 24 [25, 26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_209
  apply scheme.check_enumeration_split 25 [26, 27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_212
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_214
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {4} Certificate (by decide)
    ?_ node_216
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {4} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {4} Certificate (by decide)
    ?_ node_217
  apply scheme.check_enumeration_skip 31 [32] {4} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {4} Certificate (by decide)
  decide

theorem node_219 :
    (scheme.enumerateFrom [7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 7 [8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 8 [9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 9 [10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 10 [11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 11 [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 12 [13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 13 [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {6, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {6, 5} Certificate (by decide)
  decide

theorem node_220 :
    (scheme.enumerateFrom [14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 14 [15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 15 [16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 16 [17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 17 [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {13, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {13, 5} Certificate (by decide)
  decide

theorem node_221 :
    (scheme.enumerateFrom [18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 18 [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 19 [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {17, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {17, 16, 5} Certificate (by decide)
  decide

theorem node_222 :
    (scheme.enumerateFrom [20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 20 [21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 21 [22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 22 [23, 24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 23 [24, 25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 24 [25, 26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 25 [26, 27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 26 [27, 28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {19, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {19, 16, 5} Certificate (by decide)
  decide

theorem node_223 :
    (scheme.enumerateFrom [30, 31, 32] {29, 16, 5}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 16, 5} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 16, 5} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
