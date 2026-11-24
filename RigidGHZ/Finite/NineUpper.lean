module

public import RigidGHZ.Finite.NineNormalized4
public import RigidGHZ.Finite.NineNormalized5
public import RigidGHZ.Finite.NineNormalized6
public import RigidGHZ.Finite.NineNormalized7
public import RigidGHZ.Finite.NinePairCount
public import RigidGHZ.Finite.NineVertex
public import RigidGHZ.Supplement.MatchingRestriction

@[expose] public section
namespace RigidGHZ.Finite
set_option maxHeartbeats 10000000
set_option maxRecDepth 100000

/-- In a hypothetical 14-rigid nine-vertex triple system, every pair would have
at most four completions. The three remaining possibilities are refuted by
kernel-checked finite certificates with their ordinary hypergraph semantics. -/
theorem fourteen_codegree_le_four {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (a b : Fin 9) (hab : a ≠ b) :
    (pairCompletions H a b).card ≤ 4 := by
  by_contra hn
  have hlow : 5 ≤ (pairCompletions H a b).card := by omega
  have hhigh := pairCompletions_card_le_seven H hab
  have hc : (pairCompletions H a b).card = 5 ∨
      (pairCompletions H a b).card = 6 ∨ (pairCompletions H a b).card = 7 := by omega
  obtain ⟨f,hfa,hfb,hN⟩ := normalize_pair H hab
  have hKU := hU.relabel f
  have FK := F.relabel f
  rcases hc with h5 | h6 | h7
  · exact no_fourteen_normalized_5 _ hKU FK (by simpa only [NormalizedNinePair,h5] using hN)
  · exact no_fourteen_normalized_6 _ hKU FK (by simpa only [NormalizedNinePair,h6] using hN)
  · exact no_fourteen_normalized_7 _ hKU FK (by simpa only [NormalizedNinePair,h7] using hN)

/-- There is no 14-rigid 3-uniform hypergraph on nine vertices. -/
theorem no_fourteen_on_nine {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) : False := by
  obtain ⟨a,b,hab,hlo⟩ := fourteen_has_pair_four hU F
  have hhi := fourteen_codegree_le_four hU F a b hab
  have hc : (pairCompletions H a b).card = 4 := by omega
  obtain ⟨f,hfa,hfb,hN⟩ := normalize_pair H hab
  have hKU := hU.relabel f
  have FK := F.relabel f
  apply no_fourteen_normalized_4 _ hKU FK (by simpa only [NormalizedNinePair,hc] using hN)
  exact fourteen_codegree_le_four hKU FK

/-- The unrestricted nine-vertex extremal upper bound, for ordinary rigidity. -/
theorem nine_vertex_upper {H : Hypergraph (Fin 9)} {d : ℕ}
    (hU : Uniform H 3) (hR : IsRigid H d) : d ≤ 13 := by
  classical
  by_contra hn
  have hd : 14 ≤ d := by omega
  obtain ⟨F⟩ := hR
  obtain ⟨K,hKH,⟨RK⟩⟩ := F.exists_restriction (d := 14)
    (by simpa only [Fintype.card_fin] using hd)
  exact no_fourteen_on_nine (hU.mono hKH) RK

/-- The exact unrestricted value `f₃(9) = 13`, expressed as attainment together
with the universal upper bound over all ordinary 3-uniform hypergraphs. -/
theorem nine_vertex_exact :
    (∃ H : Hypergraph (Fin 9), Uniform H 3 ∧ IsRigid H 13) ∧
    (∀ H : Hypergraph (Fin 9), ∀ d : ℕ, Uniform H 3 → IsRigid H d → d ≤ 13) := by
  exact ⟨thirteen_witness,fun _ _ hU hR => nine_vertex_upper hU hR⟩

end RigidGHZ.Finite
