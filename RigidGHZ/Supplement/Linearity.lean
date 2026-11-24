module

public import RigidGHZ.Supplement.Grafting

/-! Linearity and the pair-codegree consequence of grafting. -/

@[expose] public section

namespace RigidGHZ.Supplement

open UpperBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

 def IsLinear (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1

 theorem linear_iff_pair_bound (H : Hypergraph V) : IsLinear H ↔ maxDegree H 2 ≤ 1 := by
  constructor
  · intro h
    apply maxDegree_le
    intro X hX
    by_contra hn
    have htwo : 1 < (H.filter (fun e => X ⊆ e)).card := by
      change ¬(H.filter (fun e => X ⊆ e)).card ≤ 1 at hn
      omega
    obtain ⟨e, he, f, hf, hef⟩ := Finset.one_lt_card.mp htwo
    obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he
    obtain ⟨hfH, hXf⟩ := Finset.mem_filter.mp hf
    have hsub : X ⊆ e ∩ f := Finset.subset_inter hXe hXf
    have hc := (Finset.card_le_card hsub).trans (h e heH f hfH hef)
    omega
  · intro h e he f hf hef
    by_contra hn
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < (e ∩ f).card)
    have hX : ({a, b} : Finset V).card = 2 := by simp [hab]
    have hsub : ({e, f} : Hypergraph V) ⊆ H.filter (fun g => ({a, b} : Finset V) ⊆ g) := by
      intro g hg
      rcases Finset.mem_insert.mp hg with rfl | hg
      · exact Finset.mem_filter.mpr ⟨he, Finset.insert_subset_iff.mpr
          ⟨(Finset.mem_inter.mp ha).1, Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hb).1⟩⟩
      · have hgf := Finset.mem_singleton.mp hg
        subst g
        exact Finset.mem_filter.mpr ⟨hf, Finset.insert_subset_iff.mpr
          ⟨(Finset.mem_inter.mp ha).2, Finset.singleton_subset_iff.mpr (Finset.mem_inter.mp hb).2⟩⟩
    have hcard := Finset.card_le_card hsub
    have hbase : codegree H {a, b} ≤ maxDegree H 2 := by
      simpa only [hX] using codegree_le_maxDegree H ({a, b} : Finset V)
    have hmax : codegree H {a, b} ≤ 1 := hbase.trans h
    have hp : ({e, f} : Hypergraph V).card = 2 := by simp [hef]
    change ({e, f} : Hypergraph V).card ≤ codegree H {a, b} at hcard
    omega

 theorem grafting_linear {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    {H : Hypergraph V} {S : Hypergraph W} {r m q : ℕ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) (hcard : Fintype.card V = r * m)
    (hH : Uniform H r) (L : RigidFamily H I) (hS : BalancedPartite S r q)
    (R : RigidFamily S I) (hLH : IsLinear H) (hLS : IsLinear S) :
    ∃ G : Hypergraph (Fin (r * (m + q - 1))), Uniform G r ∧
      Nonempty (RigidFamily G I) ∧ IsLinear G := by
  obtain ⟨G, hUG, hRG, hD⟩ := grafting hr hm hq hcard hH L hS R
  refine ⟨G, hUG, hRG, (linear_iff_pair_bound G).mpr ?_⟩
  exact (hD 2 (by decide)).trans
    (max_le ((linear_iff_pair_bound H).mp hLH) ((linear_iff_pair_bound S).mp hLS))

end RigidGHZ.Supplement
