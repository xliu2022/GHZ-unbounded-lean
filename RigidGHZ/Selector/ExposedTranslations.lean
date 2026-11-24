module

public import Mathlib.LinearAlgebra.Pi
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Basic.Real.Basic

/-!
# Exposed translations and the tripartite selector

This file proves the sum argument of Lemma 3.3 of Li--Liu and its
permutation-coordinate formulation. A coordinate perfect matching has one
edge `(a, p a, c a)` at each first-part vertex, where both `p` and `c` are
bijections. All cycle covers of the projection are explicitly accounted for
by the hypothesis `covers_complete`.
-/

@[expose] public section

namespace RigidGHZ.Selector

open scoped BigOperators

variable {I A C E : Type*}
variable [AddCommGroup E] [Module ℝ E]

/-- Each translation is the unique minimizer of its assigned linear functional. -/
def ExposedTranslations (v : I → E) (L : I → E →ₗ[ℝ] ℝ) : Prop :=
  ∀ i j, j ≠ i → L i (v i) < L i (v j)

/-- A zero sum of differences from an exposed translation uses that translation only. -/
theorem exposed_sum_purity [Fintype A]
    (v : I → E) (L : I → E →ₗ[ℝ] ℝ)
    (hexposed : ExposedTranslations v L)
    (i : I) (j : A → I)
    (hsum : ∑ a, (v (j a) - v i) = 0) :
    ∀ a, j a = i := by
  classical
  have hnonneg : ∀ a : A, 0 ≤ L i (v (j a) - v i) := by
    intro a
    by_cases h : j a = i
    · simp [h]
    · rw [map_sub]
      exact sub_nonneg.mpr (le_of_lt (hexposed i (j a) h))
  have hscalar : ∑ a, L i (v (j a) - v i) = 0 := by
    simpa only [map_sum, map_zero] using congrArg (L i) hsum
  have heach := (Finset.sum_eq_zero_iff_of_nonneg
    (fun a (_ : a ∈ (Finset.univ : Finset A)) => hnonneg a)).mp hscalar
  intro a
  by_contra h
  have hstrict := hexposed i (j a) h
  have hz := heach a (Finset.mem_univ a)
  rw [map_sub] at hz
  exact (ne_of_lt hstrict) (sub_eq_zero.mp hz).symm

/-- Distinct exposed translations are distinct vectors. -/
theorem exposed_injective (v : I → E) (L : I → E →ₗ[ℝ] ℝ)
    (h : ExposedTranslations v L) : Function.Injective v := by
  intro i j hij
  by_contra hne
  have hlt := h j i hne
  rw [hij] at hlt
  exact lt_irrefl _ hlt

/-- Membership in the union of the prescribed coordinate matchings. -/
def SupportedEdge (p : I → Equiv.Perm A) (c : I → A ≃ C)
    (a b : A) (t : C) : Prop :=
  ∃ i, b = p i a ∧ t = c i a

/-- Different prescribed coordinate matchings cannot contain the same edge. -/
theorem exposed_edge_disjoint
    (p : I → Equiv.Perm A) (c : I → A ≃ C)
    (value : C → E) (anchor : A → A → E)
    (v : I → E) (L : I → E →ₗ[ℝ] ℝ)
    (htag : ∀ i a, value (c i a) = anchor a (p i a) + v i)
    (hexposed : ExposedTranslations v L)
    {i j : I} {a : A} (hp : p i a = p j a) (hc : c i a = c j a) :
    i = j := by
  apply exposed_injective v L hexposed
  have h := congrArg value hc
  rw [htag, htag, hp] at h
  exact add_left_cancel h

/--
The coordinate form of the exposed-translation selector lemma.

All `p i` are cycle covers of the projection. `covers_complete` says that every
permutation supported by the union of their arcs is one of these covers.
The tag maps `c i` enumerate exactly the same third part, with no repetition.
Consequently every coordinate perfect matching supported by the edge union is
one of the prescribed matchings. Together with `exposed_edge_disjoint`, this
is precisely rigidity in permutation coordinates.
-/
theorem exposed_selector_complete [Fintype A] [Fintype C]
    (p : I → Equiv.Perm A) (c : I → A ≃ C)
    (value : C → E) (anchor : A → A → E)
    (v : I → E) (L : I → E →ₗ[ℝ] ℝ)
    (htag : ∀ i a, value (c i a) = anchor a (p i a) + v i)
    (hexposed : ExposedTranslations v L)
    (covers_complete : ∀ q : Equiv.Perm A,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (q : Equiv.Perm A) (t : A ≃ C)
    (hsupported : ∀ a, SupportedEdge p c a (q a) (t a)) :
    ∃ i, q = p i ∧ t = c i := by
  classical
  obtain ⟨i, hq⟩ := covers_complete q (fun a => by
    obtain ⟨j, hj, _⟩ := hsupported a
    exact ⟨j, hj⟩)
  choose j hjp hjc using hsupported
  have hpoint (a : A) :
      v (j a) - v i = value (t a) - value (c i a) := by
    rw [hjc, htag, htag]
    have hp : p (j a) a = p i a := by
      rw [← hjp, hq]
    rw [hp]
    simp
  have hsum : ∑ a, (v (j a) - v i) = 0 := by
    calc
      ∑ a, (v (j a) - v i)
          = ∑ a, (value (t a) - value (c i a)) := by
            apply Finset.sum_congr rfl
            intro a _
            exact hpoint a
      _ = (∑ a, value (t a)) - ∑ a, value (c i a) :=
        by rw [Finset.sum_sub_distrib]
      _ = 0 := by rw [t.sum_comp value, (c i).sum_comp value, sub_self]
  have hj := exposed_sum_purity v L hexposed i j hsum
  refine ⟨i, hq, ?_⟩
  ext a
  simpa only [hj a] using hjc a

end RigidGHZ.Selector
