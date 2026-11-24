module

public import RigidGHZ.SupportProduct
public import RigidGHZ.Construction.CyclicBaseline
public import RigidGHZ.Construction.ParameterChoice

/-! Canonical vertex sets and the common-parts product used in the growth theorem. -/

@[expose] public section

namespace RigidGHZ.Growth

/-- Existence on the standard balanced vertex set, with ordinary hypergraph rigidity. -/
def ExistsRigid (r m d : ℕ) : Prop :=
  ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H d

theorem canonical_exists {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d : ℕ} (hU : Uniform H r)
    (hP : BalancedPartite H r m) (hR : IsRigid H d) : ExistsRigid r m d := by
  classical
  obtain ⟨f, hf⟩ := hP.canonical
  exact ⟨relabelHypergraph f H, hU.relabel f,
    by simpa only [Fintype.card_fin] using balancedPartite_of_transversal _ hf,
    hR.relabel f⟩

theorem one_matching (r m : ℕ) (hr : 1 ≤ r) : ExistsRigid r m 1 := by
  classical
  let p : Fin 1 → Fin r → Equiv.Perm (Fin m) := fun _ _ => Equiv.refl _
  have hR : RigidFamily (coordinateHypergraph (fun i a w => p i a w)) (Fin 1) := by
    apply rigidFamily_of_coordinates ⟨0, by omega⟩ p
    · intro i; rfl
    · intro i j hij w
      exact (hij (Subsingleton.elim i j)).elim
    · intro q hq0 hq
      refine ⟨0, ?_⟩
      funext a
      apply Equiv.ext
      intro w
      obtain ⟨i, hi⟩ := hq w
      exact hi a
  exact ⟨coordinateHypergraph (fun i a w => p i a w),
    by simpa only [Fintype.card_fin] using coordinateHypergraph_uniform (fun i a w => p i a w),
    by simpa only [Fintype.card_fin] using coordinateHypergraph_balanced (fun i a w => p i a w),
    ⟨hR⟩⟩

theorem cyclic_baseline {r m : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m) :
    ExistsRigid r m (2 ^ (r - 1)) := by
  obtain ⟨H, hU, hP, hR⟩ := Cyclic.baseline r m hr hm
  exact canonical_exists hU hP hR

/-- Taking `k` copies of a proved supported factor gives the claimed power of
its matching count. Packing the supports is part of `support_product`. -/
theorem product_of_factor {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (k : ℕ) (H : Hypergraph (Fin 3 × W)) (R : RigidFamily H I) (U : Finset W)
    (hbound : k * U.card ≤ Fintype.card W)
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x)
    (hsupport : ∀ x : Fin 3 → W, tupleEdge x ∈ H →
      (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) :
    ExistsRigid (k + 2) (Fintype.card W) ((Fintype.card I) ^ k) := by
  classical
  have hb : (∑ _ : Fin k, U.card) ≤ Fintype.card W := by simpa using hbound
  obtain ⟨G, hUG, hPG, hRG⟩ := support_product (J := fun _ : Fin k => I)
    (fun _ => H) (fun _ => R) (fun _ => U) hb (fun _ => htrans) (fun _ => hsupport)
  have h := canonical_exists hUG hPG hRG
  simpa using h

theorem product_of_factor_card {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    {k m q : ℕ} (hcW : Fintype.card W = m) (hcI : Fintype.card I = q)
    (H : Hypergraph (Fin 3 × W)) (R : RigidFamily H I) (U : Finset W)
    (hbound : k * U.card ≤ m)
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x)
    (hsupport : ∀ x : Fin 3 → W, tupleEdge x ∈ H →
      (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) :
    ExistsRigid (k + 2) m (q ^ k) := by
  have h := product_of_factor k H R U (by simpa only [hcW] using hbound) htrans hsupport
  simpa only [hcW, hcI] using h

/-- Deleting complete prescribed matching classes preserves rigidity. -/
theorem ExistsRigid.restrict {r m d d' : ℕ} (h : ExistsRigid r m d)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hd : d' ≤ d) : ExistsRigid r m d' := by
  classical
  letI : Nonempty (Fin r × Fin m) := ⟨(⟨0, by omega⟩, ⟨0, by omega⟩)⟩
  obtain ⟨H, hU, hP, ⟨R⟩⟩ := h
  let e : Fin d' ↪ Fin d := ⟨Fin.castLE hd,
    fun a b h => Fin.ext (congrArg (fun x : Fin d => x.val) h)⟩
  let s := Finset.univ.map e
  have hs : s.card = d' := by simp [s]
  have hsub : s.biUnion R.matching ⊆ H := by
    intro edge he
    obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
    exact R.mem_iff.mpr ⟨i, hei⟩
  refine ⟨s.biUnion R.matching, fun edge he => hU edge (hsub he), ?_, ?_⟩
  · obtain ⟨color, hparts, hedges⟩ := hP
    exact ⟨color, hparts, fun edge he => hedges edge (hsub he)⟩
  · let f : Fin d' ≃ ↥s := Fintype.equivOfCardEq (by simp [hs])
    exact ⟨(R.restrict s).reindex f⟩

end RigidGHZ.Growth
