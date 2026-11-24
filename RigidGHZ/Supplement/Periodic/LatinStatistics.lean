module

public import RigidGHZ.Supplement.Periodic.LatinCatalogue
public import RigidGHZ.Supplement.Periodic.EnumerationStats
public import RigidGHZ.Supplement.Periodic.SmallCodes

/-! Exact finite configuration statistics from Supplement S2. The literal list
is certified equal to the proved-complete search output. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

namespace RigidGHZ.Supplement.Periodic.Latin

theorem catalogue_correct : catalogue = scheme.configurationSet := by
  rw [← catalogue_toFinset, ← enumeration_eq_list,
    bits.enumerate_eq groups ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateGroups_finset groups groups_pairwise groups_cover
    (fun A hA => groups_unique hA)

theorem configuration_count : scheme.configurationSet.card = 84 := by
  rw [← catalogue_correct]
  decide

theorem configurations_count : Fintype.card scheme.Configurations = 84 := by
  rw [scheme.configurations_card, configuration_count]

theorem transition_count : scheme.transitions.card = 20 := by
  rw [← Finset.card_image_of_injective scheme.transitions finitePairCode_injective]
  rw [Scheme.transitions, Finset.image_image, ← catalogue_correct]
  decide

theorem state_count : scheme.states.card = 14 := by
  rw [← Finset.card_image_of_injective scheme.states finiteSetCode_injective]
  unfold Scheme.states Scheme.transitions
  simp only [Finset.image_union, Finset.image_image]
  rw [← catalogue_correct]
  decide

theorem size_distribution :
    (List.range 9).map (fun k => (scheme.configurationSet.filter (fun A => A.card = k)).card) =
      [0, 0, 0, 0, 0, 0, 0, 0, 84] := by
  rw [← catalogue_correct]
  decide

def weightedArcs : List ((Finset (Fin 24) × Finset (Fin 24)) × ℕ) :=
  [(({10}, {8}), 5),
    (({10}, {10}), 1),
    (({10}, {11}), 6),
    (({8, 10}, {8, 11}), 3),
    (({8, 10}, {10, 11}), 5),
    (({11}, {8}), 7),
    (({11}, {11}), 1),
    (({8, 11}, {8, 11}), 1),
    (({10, 11}, {8, 10}), 1),
    (({10, 11}, {8, 11}), 9),
    (({8, 10, 11}, {8, 10, 11}), 1),
    (({8, 20}, {8, 20}), 1),
    (({8, 20}, {10, 20}), 13),
    (({8, 20}, {11, 20}), 2),
    (({8, 10, 20}, {8, 10, 20}), 1),
    (({8, 10, 20}, {10, 11, 20}), 4),
    (({8, 11, 20}, {8, 10, 20}), 12),
    (({8, 11, 20}, {8, 11, 20}), 1),
    (({8, 11, 20}, {10, 11, 20}), 9),
    (({8, 10, 11, 20}, {8, 10, 11, 20}), 1)]

theorem weightedArcs_support : scheme.transitions = (weightedArcs.map Prod.fst).toFinset := by
  rw [Scheme.transitions, ← catalogue_correct]
  decide

theorem weightedArcs_counts : ∀ p ∈ weightedArcs,
    scheme.transferMatrix p.1.1 p.1.2 = p.2 := by
  have hcheck : weightedArcs.all (fun p => decide
      ((catalogue.filter (fun A => scheme.input A = p.1.1 ∧ scheme.output A = p.1.2)).card = p.2)) = true := by
    decide
  intro p hp
  rw [scheme.transferMatrix_eq_filter, ← catalogue_correct]
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) p hp)

theorem every_configuration_size {A : Finset (Fin 64)} (hA : scheme.LocalConfig A) : A.card = 8 := by
  have hcheck : catalogueList.all (fun A => decide (A.card = 8)) = true := by decide
  have hm : A ∈ catalogue := by rw [catalogue_correct]; exact scheme.mem_configurationSet A |>.mpr hA
  have hl : A ∈ catalogueList := by simpa only [catalogue, Finset.mem_mk, Multiset.mem_coe] using hm
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) A hl)

end RigidGHZ.Supplement.Periodic.Latin
