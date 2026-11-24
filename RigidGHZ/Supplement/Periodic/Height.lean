module

public import RigidGHZ.Supplement.Periodic.Transfer
public import Mathlib.GroupTheory.Perm.Fin

/-! Height and odd-period certificates for cyclic sequences of states. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic

 theorem finRotate_constant {q : ℕ} (hq : 0 < q) {X : Type*} (f : Fin q → X)
    (hf : ∀ j, f (finRotate q j) = f j) : ∀ i j, f i = f j := by
  cases q with
  | zero => omega
  | succ q =>
    have hzero : ∀ i : Fin (q + 1), f i = f 0 := by
      intro i
      induction i using Fin.induction with
      | zero => rfl
      | succ i ih =>
        have hrot : finRotate (q + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
        rw [← hrot, hf]
        exact ih
    exact fun i j => (hzero i).trans (hzero j).symm

 theorem height_eq_of_monotone {L : Type*} [Fintype L] (σ : Equiv.Perm L) (h : L → ℕ)
    (hmono : ∀ j, h j ≤ h (σ j)) : ∀ j, h j = h (σ j) := by
  classical
  have hs : (∑ j, h j) = ∑ j, h (σ j) := by
    symm
    apply Finset.sum_bij (fun j _ => σ j)
    · intro j hj; exact Finset.mem_univ _
    · intro i hi j hj hij; exact σ.injective hij
    · intro j hj; exact ⟨σ.symm j, Finset.mem_univ _, σ.apply_symm_apply j⟩
    · intro j hj; rfl
  exact fun j => (Finset.sum_eq_sum_iff_of_le (fun i _ => hmono i)).mp hs j (Finset.mem_univ j)

 theorem strict_height_forces_loops {L S : Type*} [Fintype L] (σ : Equiv.Perm L)
    (state : L → S) (height : S → ℕ)
    (hstep : ∀ j, state j = state (σ j) ∨ height (state j) < height (state (σ j))) :
    ∀ j, state j = state (σ j) := by
  have hm : ∀ j, height (state j) ≤ height (state (σ j)) := by
    intro j
    rcases hstep j with h | h
    · rw [h]
    · exact h.le
  have he := height_eq_of_monotone σ (height ∘ state) hm
  intro j
  rcases hstep j with h | h
  · exact h
  · have hj := he j
    exact (Nat.ne_of_lt h hj).elim

/-- A single exceptional two-cycle cannot occur in an odd cyclic sequence;
all other equal-height arcs are loops, and its two vertices have no loops. -/
theorem odd_height_forces_loops {q : ℕ} (hq : 0 < q) (hodd : Odd q) {S : Type*}
    (R : S → S → Prop) (height : S → ℕ) (x y : S) (hxy : x ≠ y)
    (hmono : ∀ s t, R s t → height s ≤ height t)
    (hflat : ∀ s t, R s t → height s = height t →
      s = t ∨ (s = x ∧ t = y) ∨ (s = y ∧ t = x))
    (hnx : ¬R x x) (hny : ¬R y y)
    (state : Fin q → S) (hwalk : ∀ j, R (state j) (state (finRotate q j))) :
    ∀ j, state j = state (finRotate q j) := by
  classical
  let σ := finRotate q
  have he := height_eq_of_monotone σ (height ∘ state) (fun j => hmono _ _ (hwalk j))
  have hc : ∀ j, state j = state (σ j) ∨
      (state j = x ∧ state (σ j) = y) ∨ (state j = y ∧ state (σ j) = x) :=
    fun j => hflat _ _ (hwalk j) (he j)
  let bad : Fin q → Prop := fun j => state j = x ∨ state j = y
  have hb : ∀ j, bad (σ j) ↔ bad j := by
    intro j
    rcases hc j with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · simp only [bad, h]
    · simp only [bad, h1, h2]
      tauto
    · simp only [bad, h1, h2]
      tauto
  have hyx : ∀ j, state (σ j) = y ↔ state j = x := by
    intro j
    rcases hc j with h | ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hxj : state j ≠ x := by
        intro hj
        apply hnx
        have hR : R (state j) (state (σ j)) := hwalk j
        simpa only [← h, hj] using hR
      have hyj : state j ≠ y := by
        intro hj
        apply hny
        have hR : R (state j) (state (σ j)) := hwalk j
        simpa only [← h, hj] using hR
      simp only [← h, hxj, hyj]
    · simp only [h1, h2]
    · simp only [h1, h2, hxy, Ne.symm hxy]
  intro j
  by_contra hj
  have hbj : bad j := by
    rcases hc j with h | h | h
    · exact (hj h).elim
    · exact Or.inl h.1
    · exact Or.inr h.1
  have hall : ∀ k, bad k := by
    intro k
    have heq := finRotate_constant hq bad (fun k => propext (hb k)) k j
    rw [heq]
    exact hbj
  let X : Finset (Fin q) := Finset.univ.filter (fun k => state k = x)
  let Y : Finset (Fin q) := Finset.univ.filter (fun k => state k = y)
  have hcard : X.card = Y.card := by
    apply Finset.card_bij (fun k _ => σ k)
    · intro k hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hyx k).mpr (Finset.mem_filter.mp hk).2⟩
    · intro i hi k hk hik
      exact σ.injective hik
    · intro k hk
      refine ⟨σ.symm k, ?_, σ.apply_symm_apply k⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, (hyx _).mp ?_⟩
      simpa only [Equiv.apply_symm_apply] using (Finset.mem_filter.mp hk).2
  have hdis : Disjoint X Y := by
    apply Finset.disjoint_left.mpr
    intro k hkX hkY
    exact hxy ((Finset.mem_filter.mp hkX).2.symm.trans (Finset.mem_filter.mp hkY).2)
  have hcover : X ∪ Y = Finset.univ := by
    ext k
    simp only [X, Y, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
    exact hall k
  have hqcard : q = X.card + Y.card := by
    have h := congrArg Finset.card hcover
    rw [Finset.card_union_of_disjoint hdis, Finset.card_univ, Fintype.card_fin] at h
    exact h.symm
  obtain ⟨k, hk⟩ := hodd
  omega

end RigidGHZ.Supplement.Periodic
