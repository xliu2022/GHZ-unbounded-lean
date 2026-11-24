module

public import RigidGHZ.Supplement.Periodic.TenCatalogue
public import RigidGHZ.Supplement.Periodic.EnumerationStats
public import RigidGHZ.Supplement.Periodic.SmallCodes
public import RigidGHZ.Supplement.Periodic.Cardinality

/-! Exact finite configuration statistics from Supplement S2. The literal list
is certified equal to the proved-complete search output. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace RigidGHZ.Supplement.Periodic.Ten

theorem catalogue_correct : catalogue = scheme.configurationSet := by
  rw [← catalogue_toFinset, ← enumeration_eq_list,
    bits.enumerateFrom_eq (List.finRange 20) ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateFrom_finset (List.finRange 20) (List.nodup_finRange _) (by simp)

theorem configuration_count : scheme.configurationSet.card = 140 := by
  rw [← catalogue_correct]
  decide

theorem configurations_count : Fintype.card scheme.Configurations = 140 := by
  rw [scheme.configurations_card, configuration_count]

theorem transition_count : scheme.transitions.card = 123 := by
  rw [← Finset.card_image_of_injective scheme.transitions finitePairCode_injective]
  rw [Scheme.transitions, Finset.image_image, ← catalogue_correct]
  decide

theorem state_count : scheme.states.card = 55 := by
  rw [← Finset.card_image_of_injective scheme.states finiteSetCode_injective]
  unfold Scheme.states Scheme.transitions
  simp only [Finset.image_union, Finset.image_image]
  rw [← catalogue_correct]
  decide

theorem size_distribution :
    (List.range 5).map (fun k => (scheme.configurationSet.filter (fun A => A.card = k)).card) =
      [1, 20, 73, 44, 2] := by
  rw [← catalogue_correct]
  decide

theorem candidate_count : (∑ k ∈ Finset.range 5, Nat.choose 20 k) = 6196 := by decide

theorem outgoing_vertex_count : scheme.allOutgoing.card = 6 := by decide

theorem local_configuration_size {A : Finset (Fin 20)} (hA : scheme.LocalConfig A) :
    A.card ≤ 4 := by
  have h := scheme.local_configuration_size_bound (r := 3) (by omega) (by decide) hA
  simpa only [Fintype.card_fin, outgoing_vertex_count] using h

end RigidGHZ.Supplement.Periodic.Ten
