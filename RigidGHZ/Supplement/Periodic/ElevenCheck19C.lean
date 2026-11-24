module

public import RigidGHZ.Supplement.Periodic.ElevenCheck19B

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_624 :
    (scheme.enumerateFrom [] {32, 29, 28}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_625 :
    (scheme.enumerateFrom [30, 31, 32] {29, 28}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 28} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 28} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29, 28} Certificate (by decide)
    ?_ node_624
  decide

theorem node_626 :
    (scheme.enumerateFrom [] {32, 30, 28}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_627 :
    (scheme.enumerateFrom [31, 32] {30, 28}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 31 [32] {30, 28} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {30, 28} Certificate (by decide)
    ?_ node_626
  decide

theorem node_628 :
    (scheme.enumerateFrom [] {32, 28}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_629 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 29 [30, 31, 32] {28} Certificate (by decide)
    ?_ node_625
  apply scheme.check_enumeration_split 30 [31, 32] {28} Certificate (by decide)
    ?_ node_627
  apply scheme.check_enumeration_skip 31 [32] {28} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {28} Certificate (by decide)
    ?_ node_628
  decide

theorem node_630 :
    (scheme.enumerateFrom [] {32, 29}).all
      (fun A => decide (Certificate A)) = true := by
  decide

theorem node_631 :
    (scheme.enumerateFrom [30, 31, 32] {29}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29} Certificate (by decide)
  apply scheme.check_enumeration_split 32 [] {29} Certificate (by decide)
    ?_ node_630
  decide

end RigidGHZ.Supplement.Periodic.Eleven
