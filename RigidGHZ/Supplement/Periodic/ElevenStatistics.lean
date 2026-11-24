module

public import RigidGHZ.Supplement.Periodic.ElevenPairCodes
public import RigidGHZ.Supplement.Periodic.EnumerationStats
public import RigidGHZ.Supplement.Periodic.SmallCodes
public import RigidGHZ.Supplement.Periodic.Cardinality

/-! Exact finite configuration statistics from Supplement S2. The literal list
is certified equal to the proved-complete search output. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace RigidGHZ.Supplement.Periodic.Eleven

private theorem image_list_toFinset {α β : Type*} [DecidableEq α] [DecidableEq β]
    (L : List α) (f : α → β) : L.toFinset.image f = (L.map f).toFinset := by
  ext x
  simp

theorem catalogue_correct : catalogue = scheme.configurationSet := by
  rw [← catalogue_toFinset, ← enumeration_eq_list,
    bits.enumerateFrom_eq (List.finRange 33) ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateFrom_finset (List.finRange 33) (List.nodup_finRange _) (by simp)


theorem configuration_count : scheme.configurationSet.card = 333 := by
  rw [← catalogue_correct]
  decide


theorem configurations_count : Fintype.card scheme.Configurations = 333 := by
  rw [scheme.configurations_card, configuration_count]


theorem transition_count : scheme.transitions.card = 250 := by
  rw [← Finset.card_image_of_injective scheme.transitions finitePairCode_injective]
  rw [Scheme.transitions, Finset.image_image, ← catalogue_correct, ← catalogue_toFinset,
    image_list_toFinset]
  change (catalogueList.map (fun A => finitePairCode (scheme.input A, scheme.output A))).toFinset.card = 250
  rw [catalogue_pair_codes]
  decide


theorem state_count : scheme.states.card = 91 := by
  rw [← Finset.card_image_of_injective scheme.states finiteSetCode_injective]
  unfold Scheme.states Scheme.transitions
  simp only [Finset.image_union, Finset.image_image]
  rw [← catalogue_correct, ← catalogue_toFinset]
  simp only [image_list_toFinset]
  change ((catalogueList.map (fun A => finiteSetCode (scheme.input A))).toFinset ∪
    (catalogueList.map (fun A => finiteSetCode (scheme.output A))).toFinset).card = 91
  rw [catalogue_input_codes, catalogue_output_codes]
  decide


theorem size_distribution :
    (List.range 6).map (fun k => (scheme.configurationSet.filter (fun A => A.card = k)).card) =
      [0, 2, 80, 209, 42, 0] := by
  rw [← catalogue_correct]
  decide


theorem candidate_count : (∑ k ∈ Finset.range 6, Nat.choose 33 k) = 284274 := by decide


theorem outgoing_vertex_count : scheme.allOutgoing.card = 7 := by decide

theorem local_configuration_size {A : Finset (Fin 33)} (hA : scheme.LocalConfig A) :
    A.card ≤ 5 := by
  have h := scheme.local_configuration_size_bound (r := 3) (by omega) (by decide) hA
  simpa only [Fintype.card_fin, outgoing_vertex_count] using h

end RigidGHZ.Supplement.Periodic.Eleven
