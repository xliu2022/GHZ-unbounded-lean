module

public import RigidGHZ.Supplement.CyclicLiftDegrees

/-! The two-matching linear baseline from the final paragraph of Supplement S5. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators
open UpperBounds

variable {m : ℕ} [NeZero m]

/-- Rows `(a,a,a)` and `(a,a+1,a+2)`, written uniformly by the part index. -/
def linearBaselineMap (h : Bool) (j : Fin 3) (a : ZMod m) : ZMod m :=
  a + (j.val : ZMod m) * (bit h : ZMod m)

 def linearBaselinePerm (h : Bool) (j : Fin 3) : Equiv.Perm (ZMod m) :=
  Equiv.addRight ((j.val : ZMod m) * (bit h : ZMod m))

 theorem linearBaseline_complete (q r : Equiv.Perm (ZMod m))
    (hlocal : ∀ a, ∃ h : Bool,
      q a = linearBaselineMap h 1 a ∧ r a = linearBaselineMap h 2 a) :
    ∃ h : Bool, (∀ a, q a = linearBaselineMap h 1 a) ∧
      (∀ a, r a = linearBaselineMap h 2 a) := by
  choose h hq hr using hlocal
  have hsum : ((∑ a, bit (h a) : ℕ) : ZMod m) = 0 := by
    calc
      _ = ∑ a, (q a - a) := by
        rw [Nat.cast_sum]
        apply Finset.sum_congr rfl
        intro a ha
        rw [hq]
        simp [linearBaselineMap]
      _ = 0 := by
        rw [Finset.sum_sub_distrib, Equiv.sum_comp q (fun a => a), sub_self]
  have hdvd : m ∣ (Finset.univ.filter (fun a => h a = true)).card := by
    rw [← sum_bit]
    exact (ZMod.natCast_eq_zero_iff _ _).mp hsum
  obtain ⟨b, hb⟩ := constant_bit_of_card_dvd h (by simpa using hdvd)
  refine ⟨b, ?_, ?_⟩
  · intro a
    simpa only [hb] using hq a
  · intro a
    simpa only [hb] using hr a

 def linearBaselineFamily (hm : 3 ≤ m) :
    RigidFamily (coordinateHypergraph (linearBaselineMap (m := m))) Bool := by
  apply rigidFamily_of_coordinates 0 (linearBaselinePerm (m := m))
  · intro h
    apply Equiv.ext
    intro a
    simp [linearBaselinePerm]
  · intro h k hhk a
    refine ⟨1, ?_⟩
    intro he
    apply hhk
    apply bit_cast_injective (m := m) (by omega)
    simpa [linearBaselinePerm] using he
  · intro q hq0 hlocal
    obtain ⟨h, h1, h2⟩ := linearBaseline_complete (q 1) (q 2) (by
      intro a
      obtain ⟨h, hh⟩ := hlocal a
      exact ⟨h, hh 1, hh 2⟩)
    refine ⟨h, ?_⟩
    funext j
    apply Equiv.ext
    intro a
    fin_cases j
    · change q 0 a = linearBaselineMap h 0 a
      simpa [linearBaselineMap] using congrArg (fun z : Equiv.Perm (ZMod m) => z a) hq0
    · exact h1 a
    · exact h2 a

 theorem linearBaseline_pair (hm : 3 ≤ m) (h k : Bool) (a b : ZMod m) (i j : Fin 3)
    (hij : i ≠ j) (hi : linearBaselineMap h i a = linearBaselineMap k i b)
    (hj : linearBaselineMap h j a = linearBaselineMap k j b) :
    (fun l => linearBaselineMap h l a) = (fun l => linearBaselineMap k l b) := by
  have hcast : (i.val : ZMod m) ≠ (j.val : ZMod m) := by
    intro he
    apply hij
    apply Fin.ext
    have hv := congrArg ZMod.val he
    simpa only [ZMod.val_natCast_of_lt (lt_of_lt_of_le i.isLt hm),
      ZMod.val_natCast_of_lt (lt_of_lt_of_le j.isLt hm)] using hv
  cases h <;> cases k
  · have hab : a = b := by simpa [linearBaselineMap] using hi
    rw [hab]
  · have hi' : a = b + (i.val : ZMod m) := by simpa [linearBaselineMap] using hi
    have hj' : a = b + (j.val : ZMod m) := by simpa [linearBaselineMap] using hj
    exact (hcast (add_left_cancel (hi'.symm.trans hj'))).elim
  · have hi' : a + (i.val : ZMod m) = b := by simpa [linearBaselineMap] using hi
    have hj' : a + (j.val : ZMod m) = b := by simpa [linearBaselineMap] using hj
    exact (hcast (add_left_cancel (hi'.trans hj'.symm))).elim
  · have hab : a = b := by simpa [linearBaselineMap] using hi
    rw [hab]

/-- Every part size at least three admits a linear tripartite 2-rigid hypergraph. -/
 theorem linear_baseline (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × ZMod m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 2 ∧ maxDegree H 2 ≤ 1 := by
  let H := coordinateHypergraph (linearBaselineMap (m := m))
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · simpa using coordinateHypergraph_uniform (linearBaselineMap (m := m))
  · simpa using coordinateHypergraph_balanced (linearBaselineMap (m := m))
  · let e : Fin 2 ≃ Bool := (Fintype.equivFinOfCardEq (by simp)).symm
    exact ⟨(linearBaselineFamily hm).reindex e⟩
  · apply maxDegree_le H 2 1
    exact coordinate_codegree_one _ (linearBaseline_pair hm)

/-- A single diagonal matching is a linear rigid triple system at every part
size, covering in particular the supplementary sizes one and two. -/
 theorem linear_single (n : ℕ) :
    ∃ H : Hypergraph (Fin 3 × Fin n), Uniform H 3 ∧ BalancedPartite H 3 n ∧
      IsRigid H 1 ∧ maxDegree H 2 ≤ 1 := by
  let p : Unit → Fin 3 → Equiv.Perm (Fin n) := fun _ _ => Equiv.refl _
  let H := coordinateHypergraph (fun u j a => p u j a)
  have F : RigidFamily H Unit := by
    apply rigidFamily_of_coordinates 0 p
    · intro u
      rfl
    · intro u v huv
      exact (huv (Subsingleton.elim _ _)).elim
    · intro q hq0 hq
      refine ⟨(), ?_⟩
      funext j
      apply Equiv.ext
      intro a
      obtain ⟨u, hu⟩ := hq a
      exact hu j
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · simpa using coordinateHypergraph_uniform (fun u j a => p u j a)
  · simpa using coordinateHypergraph_balanced (fun u j a => p u j a)
  · let e : Fin 1 ≃ Unit := (Fintype.equivFinOfCardEq (by simp)).symm
    exact ⟨F.reindex e⟩
  · apply maxDegree_le H 2 1
    apply coordinate_codegree_one
    intro s t a b i j hij hi hj
    have hab : a = b := hi
    subst b
    rfl

end RigidGHZ.Supplement.Affine
