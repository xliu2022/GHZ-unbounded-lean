module

public import RigidGHZ.Construction.CyclicBaseline

/-! Supplemental Proposition S1.2: doubling the number of perfect matchings. -/

@[expose] public section

namespace RigidGHZ

variable {A W I : Type*} [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W] [Fintype I]

/-- Coordinate completeness and separation recovered from an ordinary rigid
matching family, rather than assumed as a construction interface. -/
theorem coordinates_of_rigidFamily (a0 : A) {H : Hypergraph (A × W)}
    (R : RigidFamily H I)
    (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x) :
    ∃ p : I → A → Equiv.Perm W,
      (∀ i, p i a0 = Equiv.refl W) ∧
      (∀ i, R.matching i = coordinateMatching (fun a w => p i a w)) ∧
      (∀ i j, i ≠ j → ∀ w, ∃ a, p i a w ≠ p j a w) ∧
      ∀ q : A → Equiv.Perm W, q a0 = Equiv.refl W →
        (∀ w, ∃ i, ∀ a, q a w = p i a w) → ∃ i, q = p i := by
  classical
  letI : Nonempty A := ⟨a0⟩
  have hc : ∀ i : I, ∃ p : A → Equiv.Perm W,
      p a0 = Equiv.refl W ∧ R.matching i = coordinateMatching (fun a w => p a w) := by
    intro i
    exact perfectMatching_coordinates a0 htrans (R.perfect i)
  choose p hp0 hpM using hc
  have hrow : ∀ i w, tupleEdge (fun a => p i a w) ∈ R.matching i := by
    intro i w
    rw [hpM i]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  refine ⟨p, hp0, hpM, ?_, ?_⟩
  · intro i j hij w
    by_contra h
    push_neg at h
    apply hij
    apply R.eq_of_shared_edge (hrow i w)
    simpa only [funext h] using hrow j w
  · intro q hq0 hq
    have hM : PerfectMatching H (coordinateMatching (fun a w => q a w)) := by
      apply (coordinateMatching_perfect (fun a w => q a w) (fun a => (q a).bijective)).mono
      intro e he
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨i, hi⟩ := hq w
      have heq : (fun a => q a w) = (fun a => p i a w) := funext hi
      rw [heq]
      exact (R.perfect i).subset (hrow i w)
    obtain ⟨i, hi⟩ := R.complete _ hM
    exact ⟨i, coordinates_eq_of_matching_eq a0 q (p i) hq0 (hp0 i) (hi.trans (hpM i))⟩

namespace Supplement

/-- Add one cyclic binary coordinate to every matching of an actual balanced
hypergraph. The matching count is doubled and the common part size is unchanged. -/
theorem doubling_family (a0 : A) {H : Hypergraph (A × W)}
    (R : RigidFamily H I) (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x)
    (τ : Equiv.Perm W) (hτ : τ.IsCycle) (hfree : ∀ w, τ w ≠ w) :
    ∃ G : Hypergraph (Option A × W),
      Uniform G (Fintype.card A + 1) ∧
      BalancedPartite G (Fintype.card A + 1) (Fintype.card W) ∧
      Nonempty (RigidFamily G (I × Bool)) := by
  classical
  obtain ⟨p, hp0, hpM, hpsep, hpcomplete⟩ := coordinates_of_rigidFamily a0 R htrans
  let q : (I × Bool) → Option A → Equiv.Perm W := fun ib a => match a with
    | none => Cyclic.binaryPerm τ ib.2
    | some a => p ib.1 a
  have hq0 : ∀ ib, q ib (some a0) = Equiv.refl W := fun ib => hp0 ib.1
  have hqsep : ∀ i j, i ≠ j → ∀ w, ∃ a, q i a w ≠ q j a w := by
    intro i j hij w
    by_cases hi : i.1 = j.1
    · have hb : i.2 ≠ j.2 := fun hb => hij (Prod.ext hi hb)
      refine ⟨none, ?_⟩
      cases hbi : i.2 <;> cases hbj : j.2 <;>
        simp_all [q, Cyclic.binaryPerm, hfree, Ne.symm (hfree w)]
    · obtain ⟨a, ha⟩ := hpsep i.1 j.1 hi w
      exact ⟨some a, ha⟩
  have hqcomplete : ∀ z : Option A → Equiv.Perm W, z (some a0) = Equiv.refl W →
      (∀ w, ∃ i, ∀ a, z a w = q i a w) → ∃ i, z = q i := by
    intro z hz0 hz
    obtain ⟨i, hi⟩ := hpcomplete (fun a => z (some a)) hz0 (by
      intro w
      obtain ⟨ib, hib⟩ := hz w
      exact ⟨ib.1, fun a => hib (some a)⟩)
    have hnew : z none = Equiv.refl W ∨ z none = τ := by
      apply Cyclic.two_choices_on_cycle τ (z none) hτ
      intro w
      obtain ⟨ib, hib⟩ := hz w
      have ha := hib none
      cases hb : ib.2
      · exact Or.inl (by simpa [q, Cyclic.binaryPerm, hb] using ha)
      · exact Or.inr (by simpa [q, Cyclic.binaryPerm, hb] using ha)
    obtain ⟨b, hb⟩ : ∃ b : Bool, z none = Cyclic.binaryPerm τ b := by
      rcases hnew with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    refine ⟨(i, b), ?_⟩
    funext a
    cases a with
    | none => exact hb
    | some a => exact congrFun hi a
  let G := coordinateHypergraph (fun ib a w => q ib a w)
  refine ⟨G, ?_, ?_, ⟨rigidFamily_of_coordinates (some a0) q hq0 hqsep hqcomplete⟩⟩
  · simpa only [Fintype.card_option] using coordinateHypergraph_uniform (fun ib a w => q ib a w)
  · simpa only [Fintype.card_option] using coordinateHypergraph_balanced_card (fun ib a w => q ib a w)

/-- Proposition S1.2, on ordinary hypergraphs and standard finite vertex sets. -/
theorem doubling {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d : ℕ} (hr : 2 ≤ r) (hm : 2 ≤ m)
    (hpart : BalancedPartite H r m) (hrigid : IsRigid H d) :
    ∃ G : Hypergraph (Fin (r + 1) × Fin m),
      Uniform G (r + 1) ∧ BalancedPartite G (r + 1) m ∧ IsRigid G (2 * d) := by
  classical
  obtain ⟨f, htrans⟩ := hpart.canonical
  obtain ⟨R⟩ := hrigid
  let τ := finRotate m
  have hτ : τ.IsCycle := isCycle_finRotate_of_le hm
  have hfree : ∀ w, τ w ≠ w := by
    intro w
    apply Equiv.Perm.mem_support.mp
    rw [show τ.support = Finset.univ from support_finRotate_of_le hm]
    exact Finset.mem_univ _
  obtain ⟨G, hUG, hPG, ⟨RG⟩⟩ := doubling_family (⟨0, by omega⟩ : Fin r)
    (R.relabel f) htrans τ hτ hfree
  have hP : BalancedPartite G (r + 1) m := by simpa using hPG
  obtain ⟨g, hg⟩ := hP.canonical
  let e : Fin (2 * d) ≃ (Fin d × Bool) :=
    (Fintype.equivFinOfCardEq (by simp [mul_comm])).symm
  refine ⟨relabelHypergraph g G, ?_, ?_, ⟨(RG.reindex e).relabel g⟩⟩
  · simpa using hUG.relabel g
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal _ hg

end Supplement
end RigidGHZ
