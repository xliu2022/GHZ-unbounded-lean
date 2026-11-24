module

public import RigidGHZ.Selector.ExposedTranslations
public import Mathlib.Data.Nat.Choose.Cast
public import Mathlib.Tactic.Ring

/-!
# Parabolic translations

Exact exposure identities used in the planar and rectangular constructions.
The natural-number coordinates are the binomial coefficients printed in the
paper, not an asymptotic or approximate parabola.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.Selector

/-- The real polynomial agreeing with `Nat.choose n 2` at natural numbers. -/
def triangular (x : ℝ) : ℝ := x * (x - 1) / 2

theorem triangular_nat (n : ℕ) : triangular n = (n.choose 2 : ℝ) := by
  rw [Nat.cast_choose_two]
  rfl

/-- Planar translations used by the one-row construction. -/
def planarTranslation (a : ℝ) : Fin 2 → ℝ := ![a, triangular a]

/-- A linear functional exposing the point of index `a`. -/
def planarFunctional (a : ℝ) : (Fin 2 → ℝ) →ₗ[ℝ] ℝ :=
  2 • LinearMap.proj 1 - (2 * a - 1) • LinearMap.proj 0

theorem planar_exposure_identity (a b : ℝ) :
    planarFunctional a (planarTranslation b - planarTranslation a) = (b - a) ^ 2 := by
  simp [planarFunctional, planarTranslation, triangular]
  ring

theorem planar_exposed : ExposedTranslations planarTranslation planarFunctional := by
  intro a b hba
  have hp : 0 < (b - a) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hba)
  rw [← planar_exposure_identity, map_sub] at hp
  exact sub_pos.mp hp

/-- Rectangular translations indexed by a row and an exit. -/
def rectangularTranslation (a : ℝ × ℝ) : Fin 3 → ℝ :=
  ![a.1, a.2, triangular a.1 + triangular a.2]

/-- The functional in equation (3.2) of the article. -/
def rectangularFunctional (a : ℝ × ℝ) : (Fin 3 → ℝ) →ₗ[ℝ] ℝ :=
  2 • LinearMap.proj 2 - (2 * a.1 - 1) • LinearMap.proj 0
    - (2 * a.2 - 1) • LinearMap.proj 1

theorem rectangular_exposure_identity (a b : ℝ × ℝ) :
    rectangularFunctional a (rectangularTranslation b - rectangularTranslation a)
      = (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
  simp [rectangularFunctional, rectangularTranslation, triangular]
  ring

theorem rectangular_exposed :
    ExposedTranslations rectangularTranslation rectangularFunctional := by
  intro a b hba
  have hp : 0 < (b.1 - a.1) ^ 2 + (b.2 - a.2) ^ 2 := by
    by_cases h₁ : b.1 = a.1
    · have h₂ : b.2 ≠ a.2 := by
        intro h₂
        exact hba (Prod.ext h₁ h₂)
      exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero (sub_ne_zero.mpr h₂))
    · exact add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero (sub_ne_zero.mpr h₁)) (sq_nonneg _)
  rw [← rectangular_exposure_identity, map_sub] at hp
  exact sub_pos.mp hp

/-- Restricting an exposed family along an injection preserves exposure. -/
theorem ExposedTranslations.comp {I J E : Type*} [AddCommGroup E] [Module ℝ E]
    {v : I → E} {L : I → E →ₗ[ℝ] ℝ} (h : ExposedTranslations v L)
    (f : J → I) (hf : Function.Injective f) :
    ExposedTranslations (v ∘ f) (L ∘ f) := by
  intro i j hji
  exact h (f i) (f j) (fun h => hji (hf h))

/-- The finite planar translations appearing in Proposition A.3. -/
theorem planar_fin_exposed (t : ℕ) :
    ExposedTranslations
      (fun a : Fin t => planarTranslation (a.val : ℝ))
      (fun a : Fin t => planarFunctional (a.val : ℝ)) := by
  apply planar_exposed.comp (fun a : Fin t => (a.val : ℝ))
  intro a b hab
  apply Fin.ext
  exact Nat.cast_injective hab

/-- The finite grid of translations appearing in Proposition A.1. -/
theorem rectangular_fin_exposed (t : ℕ) :
    ExposedTranslations
      (fun a : Fin t × Fin t => rectangularTranslation ((a.1.val : ℝ), (a.2.val : ℝ)))
      (fun a : Fin t × Fin t => rectangularFunctional ((a.1.val : ℝ), (a.2.val : ℝ))) := by
  apply rectangular_exposed.comp
    (fun a : Fin t × Fin t => ((a.1.val : ℝ), (a.2.val : ℝ)))
  intro a b hab
  apply Prod.ext
  · apply Fin.ext
    have := congrArg Prod.fst hab
    exact Nat.cast_injective this
  · apply Fin.ext
    have := congrArg Prod.snd hab
    exact Nat.cast_injective this

end RigidGHZ.Selector
