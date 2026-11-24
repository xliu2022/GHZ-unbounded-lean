module

public import RigidGHZ.Supplement.Periodic.ElevenCheck19A

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem node_616 :
    (scheme.enumerateFrom [30, 31, 32] {29, 26}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 26} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 26} Certificate (by decide)
  decide

theorem node_617 :
    (scheme.enumerateFrom [32] {31, 26}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 26} Certificate (by decide)
  decide

theorem node_618 :
    (scheme.enumerateFrom [27, 28, 29, 30, 31, 32] {26}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 27 [28, 29, 30, 31, 32] {26} Certificate (by decide)
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {26} Certificate (by decide)
    ?_ node_615
  apply scheme.check_enumeration_split 29 [30, 31, 32] {26} Certificate (by decide)
    ?_ node_616
  apply scheme.check_enumeration_skip 30 [31, 32] {26} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {26} Certificate (by decide)
    ?_ node_617
  apply scheme.check_enumeration_skip 32 [] {26} Certificate (by decide)
  decide

theorem node_619 :
    (scheme.enumerateFrom [30, 31, 32] {29, 28, 27}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 28, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 28, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 28, 27} Certificate (by decide)
  decide

theorem node_620 :
    (scheme.enumerateFrom [29, 30, 31, 32] {28, 27}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 29 [30, 31, 32] {28, 27} Certificate (by decide)
    ?_ node_619
  apply scheme.check_enumeration_skip 30 [31, 32] {28, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {28, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {28, 27} Certificate (by decide)
  decide

theorem node_621 :
    (scheme.enumerateFrom [30, 31, 32] {29, 27}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 30 [31, 32] {29, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 31 [32] {29, 27} Certificate (by decide)
  apply scheme.check_enumeration_skip 32 [] {29, 27} Certificate (by decide)
  decide

theorem node_622 :
    (scheme.enumerateFrom [32] {31, 27}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_skip 32 [] {31, 27} Certificate (by decide)
  decide

theorem node_623 :
    (scheme.enumerateFrom [28, 29, 30, 31, 32] {27}).all
      (fun A => decide (Certificate A)) = true := by
  apply scheme.check_enumeration_split 28 [29, 30, 31, 32] {27} Certificate (by decide)
    ?_ node_620
  apply scheme.check_enumeration_split 29 [30, 31, 32] {27} Certificate (by decide)
    ?_ node_621
  apply scheme.check_enumeration_skip 30 [31, 32] {27} Certificate (by decide)
  apply scheme.check_enumeration_split 31 [32] {27} Certificate (by decide)
    ?_ node_622
  apply scheme.check_enumeration_skip 32 [] {27} Certificate (by decide)
  decide

end RigidGHZ.Supplement.Periodic.Eleven
