module

public import RigidGHZ.SourceModel.Labels
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Finset.Powerset

/-!
# Finite accepted-state coefficients

An accepted state is the pushforward of the matching amplitudes to label
strings. The proved injectivity of that map shows that nonzero matching
amplitudes cannot cancel. This file isolates the exact finite-dimensional
support statement, independently of the formula used for source amplitudes.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

section Pushforward

variable {α β : Type*} [Fintype α]

/-- Add amplitudes of all alternatives that produce the same output label. -/
def finitePushforward (f : α → β) (b : α → ℂ) (y : β) : ℂ := by
  classical
  exact ∑ x, if f x = y then b x else 0

theorem finitePushforward_at_image (f : α → β) (b : α → ℂ)
    (hf : Function.Injective f) (a : α) :
    finitePushforward f b (f a) = b a := by
  classical
  simp [finitePushforward, hf.eq_iff]

theorem finitePushforward_outside (f : α → β) (b : α → ℂ)
    {y : β} (hy : y ∉ Set.range f) : finitePushforward f b y = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro a _
  have ha : f a ≠ y := fun h => hy ⟨a, h⟩
  simp [ha]

theorem finitePushforward_support (f : α → β) (b : α → ℂ)
    (hf : Function.Injective f) (hb : ∀ a, b a ≠ 0) :
    {y | finitePushforward f b y ≠ 0} = Set.range f := by
  ext y
  constructor
  · intro hy
    by_contra h
    exact hy (finitePushforward_outside f b h)
  · rintro ⟨a, rfl⟩
    change finitePushforward f b (f a) ≠ 0
    rw [finitePushforward_at_image f b hf]
    exact hb a

theorem normSq_finitePushforward [DecidableEq β] (f : α → β) (b : α → ℂ)
    (hf : Function.Injective f) (y : β) :
    Complex.normSq (finitePushforward f b y) =
      ∑ a, if f a = y then Complex.normSq (b a) else 0 := by
  classical
  by_cases hy : y ∈ Set.range f
  · obtain ⟨a, rfl⟩ := hy
    rw [finitePushforward_at_image f b hf]
    simp [hf.eq_iff]
  · rw [finitePushforward_outside f b hy, map_zero]
    symm
    apply Finset.sum_eq_zero
    intro a _
    have ha : f a ≠ y := fun h => hy ⟨a, h⟩
    simp [ha]

/-- An injective relabeling preserves the squared norm of a finite state. -/
theorem finitePushforward_normSq [Fintype β] (f : α → β) (b : α → ℂ)
    (hf : Function.Injective f) :
    ∑ y, Complex.normSq (finitePushforward f b y) = ∑ a, Complex.normSq (b a) := by
  classical
  simp_rw [normSq_finitePushforward f b hf]
  rw [Finset.sum_comm]
  simp

end Pushforward

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- There are finitely many perfect matchings, since each is a subset of `H`. -/
instance perfectMatchingsFintype (H : Hypergraph V) : Fintype (PerfectMatchings H) :=
  Fintype.ofInjective
    (fun M : PerfectMatchings H =>
      (⟨M.1, Finset.mem_powerset.mpr M.2.subset⟩ : H.powerset))
    (by
      intro M N h
      exact Subtype.ext (congrArg (fun s : H.powerset => s.1) h))

namespace MatchingDecomposition

variable (F : MatchingDecomposition H I)

/-- The coefficient of each output label string after one-photon-per-path selection. -/
def acceptedState (b : PerfectMatchings H → ℂ) : (V → I) → ℂ :=
  finitePushforward F.labelString b

theorem acceptedState_at_matching (b : PerfectMatchings H → ℂ)
    (hnonempty : ∀ e ∈ H, e.Nonempty) (M : PerfectMatchings H) :
    F.acceptedState b (F.labelString M) = b M :=
  finitePushforward_at_image F.labelString b (F.labelString_injective hnonempty) M

theorem acceptedState_support (b : PerfectMatchings H → ℂ)
    (hnonempty : ∀ e ∈ H, e.Nonempty) (hb : ∀ M, b M ≠ 0) :
    {s | F.acceptedState b s ≠ 0} = F.acceptedLabels :=
  finitePushforward_support F.labelString b (F.labelString_injective hnonempty) hb

end MatchingDecomposition

/--
The noncancellation and support equivalence in Proposition 2.1.
Actual binary-source coefficients satisfy `hb` when all emission probabilities
lie strictly between zero and one. No equality or positivity of phases is
assumed here.
-/
theorem acceptedState_support_iff_isRigid [Nonempty V] {d : ℕ}
    (F : MatchingDecomposition H (Fin d))
    (b : PerfectMatchings H → ℂ)
    (hnonempty : ∀ e ∈ H, e.Nonempty) (hb : ∀ M, b M ≠ 0) :
    {s | F.acceptedState b s ≠ 0} = F.constantLabels ↔ IsRigid H d := by
  rw [F.acceptedState_support b hnonempty hb]
  exact acceptedLabels_eq_constantLabels_iff_isRigid F hnonempty

end RigidGHZ.SourceModel
