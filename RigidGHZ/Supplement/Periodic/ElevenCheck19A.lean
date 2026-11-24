module

public import RigidGHZ.Supplement.Periodic.ElevenCheck18

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_608 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26, 25}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {26, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {26, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {26, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {26, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {26, 25} Certificate (by decide)
  decide

theorem node_609 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27, 25}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {27, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {27, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 30 [31, 32] {27, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {27, 25} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {27, 25} Certificate (by decide)
  decide

theorem node_610 :
    (scheme.enumerateFrom [] {32, 30, 25}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_611 :
    (scheme.enumerateFrom [31, 32] {30, 25}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 25} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {30, 25} Certificate (by decide)
    ?_ node_610
  decide

theorem node_612 :
    (scheme.enumerateFrom [] {32, 25}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_613 :
    (scheme.enumerateFrom [26, 27, 28, 29, 30, 31, 32] {25}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 26 [27, 28, 29, 30, 31, 32] {25} Certificate (by decide)
    ?_ node_608
  apply scheme.check_enumeration_split 27 [28, 29, 30, 31, 32] {25} Certificate (by decide)
    ?_ node_609
  apply scheme.check_enumeration_skip 28 [29, 30, 31, 32] {25} Certificate (by decide)
  apply scheme.check_enumeration_skip 29 [30, 31, 32] {25} Certificate (by decide)
  apply scheme.check_enumeration_split 30 [31, 32] {25} Certificate (by decide)
    ?_ node_611
  apply scheme.check_enumeration_skip 31 [32] {25} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {25} Certificate (by decide)
    ?_ node_612
  decide

theorem node_614 :
    (scheme.enumerateFrom [30, 31, 32] {29, 28, 26}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 28, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 28, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 28, 26} Certificate (by decide)
  decide

theorem node_615 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 26}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 29 [30, 31, 32] {28, 26} Certificate (by decide)
    ?_ node_614
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 26} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
