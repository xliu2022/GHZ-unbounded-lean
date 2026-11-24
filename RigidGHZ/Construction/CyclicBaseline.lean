module

public import RigidGHZ.Relabel
public import Mathlib.GroupTheory.Perm.Fin

/-!
# Cyclic choices and the elementary baseline

The first theorem is Supplemental Lemma S1.1.  Independent binary choices in
the non-root parts then give the `2^(r-1)`-rigid baseline at every part size
at least two.
-/

@[expose] public section

namespace RigidGHZ.Cyclic

variable {W : Type*} [Finite W]

theorem two_choices_on_cycle (τ ρ : Equiv.Perm W) (hτ : τ.IsCycle)
    (hchoice : ∀ x, ρ x = x ∨ ρ x = τ x) : ρ = Equiv.refl W ∨ ρ = τ := by
  classical
  by_cases hid : ρ = Equiv.refl W
  · exact Or.inl hid
  · right
    have hex : ∃ x, ρ x ≠ x := by
      by_contra h
      push_neg at h
      exact hid (Equiv.ext h)
    obtain ⟨x, hx⟩ := hex
    have hρx : ρ x = τ x := (hchoice x).resolve_left hx
    have hτx : τ x ≠ x := fun h => hx (hρx.trans h)
    have hmove : ∀ n : ℕ, ρ ((τ ^ n) x) ≠ (τ ^ n) x := by
      intro n
      induction n with
      | zero => simpa using hx
      | succ n ih =>
        rw [pow_succ', Equiv.Perm.mul_apply]
        have hnext : ρ ((τ ^ n) x) = τ ((τ ^ n) x) :=
          (hchoice _).resolve_left ih
        intro hf
        have he : τ ((τ ^ n) x) = (τ ^ n) x :=
          ρ.injective (hf.trans hnext.symm)
        exact ih (hnext.trans he)
    apply Equiv.ext
    intro y
    by_cases hy : τ y = y
    · rcases hchoice y with h | h
      · exact h.trans hy.symm
      · exact h
    · obtain ⟨n, hn⟩ := hτ.exists_pow_eq hτx hy
      have hm : ρ y ≠ y := by simpa only [hn] using hmove n
      exact (hchoice y).resolve_left hm

def binaryPerm (τ : Equiv.Perm W) (b : Bool) : Equiv.Perm W :=
  if b then τ else Equiv.refl W

def binaryCoordinates {A : Type*} (τ : Equiv.Perm W) (i : A → Bool) :
    Option A → Equiv.Perm W
  | none => Equiv.refl W
  | some a => binaryPerm τ (i a)

variable {A : Type*} [Fintype A] [DecidableEq A] [Fintype W] [DecidableEq W]

def binaryRigidFamily (τ : Equiv.Perm W) (hτ : τ.IsCycle) (hfree : ∀ w, τ w ≠ w) :
    RigidFamily (coordinateHypergraph (fun (i : A → Bool) a w => binaryCoordinates τ i a w)) (A → Bool) := by
  classical
  apply rigidFamily_of_coordinates (none : Option A) (binaryCoordinates τ)
  · intro i
    rfl
  · intro i j hij w
    obtain ⟨a, ha⟩ : ∃ a, i a ≠ j a := by
      by_contra h
      push_neg at h
      exact hij (funext h)
    refine ⟨some a, ?_⟩
    cases hi : i a <;> cases hj : j a <;>
      simp_all [binaryCoordinates, binaryPerm, hfree, Ne.symm (hfree w)]
  · intro q hq0 hq
    have hc : ∀ a : A, q (some a) = Equiv.refl W ∨ q (some a) = τ := by
      intro a
      apply two_choices_on_cycle τ (q (some a)) hτ
      intro w
      obtain ⟨i, hi⟩ := hq w
      have ha := hi (some a)
      cases hbit : i a
      · exact Or.inl (by simpa [binaryCoordinates, binaryPerm, hbit] using ha)
      · exact Or.inr (by simpa [binaryCoordinates, binaryPerm, hbit] using ha)
    have hb : ∀ a : A, ∃ b : Bool, q (some a) = binaryPerm τ b := by
      intro a
      rcases hc a with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    choose i hi using hb
    refine ⟨i, ?_⟩
    funext a
    cases a with
    | none => exact hq0
    | some a => exact hi a

theorem binary_isRigid (τ : Equiv.Perm W) (hτ : τ.IsCycle) (hfree : ∀ w, τ w ≠ w) :
    IsRigid (coordinateHypergraph (fun (i : A → Bool) a w => binaryCoordinates τ i a w))
      (2 ^ Fintype.card A) := by
  classical
  have hc : Fintype.card (A → Bool) = 2 ^ Fintype.card A := by simp
  let e : (A → Bool) ≃ Fin (2 ^ Fintype.card A) := Fintype.equivFinOfCardEq hc
  exact ⟨(binaryRigidFamily τ hτ hfree).reindex e.symm⟩

theorem baseline (r m : ℕ) (hr : 2 ≤ r) (hm : 2 ≤ m) :
    ∃ H : Hypergraph (Option (Fin (r - 1)) × Fin m),
      Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H (2 ^ (r - 1)) := by
  let τ := finRotate m
  have hτ : τ.IsCycle := isCycle_finRotate_of_le hm
  have hfree : ∀ w, τ w ≠ w := by
    intro w
    have hw : w ∈ τ.support := by
      rw [show τ.support = Finset.univ from support_finRotate_of_le hm]
      exact Finset.mem_univ w
    exact Equiv.Perm.mem_support.mp hw
  let p := fun (i : Fin (r - 1) → Bool) a w => binaryCoordinates τ i a w
  refine ⟨coordinateHypergraph p, ?_, ?_, ?_⟩
  · have h := coordinateHypergraph_uniform p
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.sub_add_cancel (by omega : 1 ≤ r)] using h
  · have h := coordinateHypergraph_balanced_card p
    simpa only [Fintype.card_option, Fintype.card_fin, Nat.sub_add_cancel (by omega : 1 ≤ r)] using h
  · simpa only [Fintype.card_fin] using binary_isRigid (A := Fin (r - 1)) τ hτ hfree

end RigidGHZ.Cyclic
