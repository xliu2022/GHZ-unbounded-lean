module

public import RigidGHZ.SourceModel.Normalization
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Logic.Equiv.Set

/-!
# The Schmidt decomposition of the actual GHZ coefficient vector

For a nonempty collection of paths, the constant label strings index an
orthonormal family in its ordinary complex Euclidean coefficient space.
Splitting the paths into two nonempty parts therefore gives an explicit
Schmidt decomposition of `ghzState`: its `d` coefficients are all the positive
real number `1 / sqrt d`. The vectors and their orthonormality are constructed
and proved; no rank or Schmidt property is assumed.

The equivalence `cut : V ≃ A ⊕ B` represents an arbitrary bipartition. The
last theorem also states the result for a subset and its complement.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators Classical

/-- Distinct labels give distinct constant strings on any nonempty side. -/
theorem constantString_injective (A I : Type*) [Nonempty A] :
    Function.Injective (fun i : I => fun _ : A => i) := by
  intro i j h
  exact congrFun h (Classical.choice (inferInstance : Nonempty A))

/-- The unit coefficient vector at the constant string with label `i`. -/
def ghzSchmidtVector (A : Type*) (d : ℕ) (i : Fin d) :
    EuclideanSpace ℂ (A → Fin d) := by
  classical
  exact EuclideanSpace.single (fun _ : A => i) 1

theorem ghzSchmidtVector_apply (A : Type*) (d : ℕ) (i : Fin d)
    (a : A → Fin d) :
    ghzSchmidtVector A d i a = if a = (fun _ => i) then 1 else 0 := by
  classical
  simp [ghzSchmidtVector, PiLp.single_apply]

/-- These are genuine orthonormal vectors for the standard complex inner product. -/
theorem ghzSchmidtVector_orthonormal (A : Type*) [Fintype A] [DecidableEq A] [Nonempty A]
    (d : ℕ) : Orthonormal ℂ (ghzSchmidtVector A d) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  by_cases hij : i = j
  · subst j
    simp [ghzSchmidtVector, EuclideanSpace.inner_single_left]
  · have hc : (fun _ : A => j) ≠ (fun _ : A => i) := by
      intro h
      exact hij ((constantString_injective A (Fin d) h).symm)
    simp [ghzSchmidtVector, EuclideanSpace.inner_single_left,
      PiLp.single_apply, hc, hij]

/-- The common real Schmidt coefficient. -/
def ghzSchmidtCoefficient (d : ℕ) : ℝ := 1 / Real.sqrt (d : ℝ)

theorem ghzSchmidtCoefficient_pos {d : ℕ} (hd : 0 < d) :
    0 < ghzSchmidtCoefficient d :=
  one_div_pos.mpr (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hd))

theorem ghzSchmidtCoefficient_sq (d : ℕ) :
    ghzSchmidtCoefficient d ^ 2 = 1 / (d : ℝ) := by
  simp only [ghzSchmidtCoefficient, div_pow, one_pow,
    Real.sq_sqrt (Nat.cast_nonneg d)]

theorem ghzSchmidtCoefficient_sum_sq {d : ℕ} (hd : 0 < d) :
    (∑ _i : Fin d, ghzSchmidtCoefficient d ^ 2) = 1 := by
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)
  simp only [ghzSchmidtCoefficient_sq, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  exact mul_one_div_cancel hd'

/-- The existing GHZ definition is the sum of its distinct constant-label entries. -/
theorem ghzState_eq_finitePushforward (V : Type*) [Nonempty V] (d : ℕ) :
    ghzState V d = finitePushforward (fun i : Fin d => fun _ : V => i)
      (fun _ => (ghzSchmidtCoefficient d : ℂ)) := by
  classical
  funext s
  by_cases hs : s ∈ Set.range (fun i : Fin d => fun _ : V => i)
  · obtain ⟨i, rfl⟩ := hs
    rw [finitePushforward_at_image _ _ (constantString_injective V (Fin d))]
    simp [ghzState, ghzSchmidtCoefficient]
  · rw [finitePushforward_outside _ _ hs]
    simp [ghzState, hs]

/-- The coefficient matrix of `ghzState` after an arbitrary split of the paths. -/
def ghzCoefficientMatrix {V A B : Type*} (cut : V ≃ A ⊕ B) (d : ℕ) :
    Matrix (A → Fin d) (B → Fin d) ℂ :=
  fun a b => ghzState V d (fun v => Sum.elim a b (cut v))

theorem joined_constant_iff {V A B I : Type*} (cut : V ≃ A ⊕ B)
    (a : A → I) (b : B → I) (i : I) :
    (fun v => Sum.elim a b (cut v)) = (fun _ => i) ↔
      a = (fun _ => i) ∧ b = (fun _ => i) := by
  constructor
  · intro h
    constructor
    · funext x
      simpa using congrFun h (cut.symm (Sum.inl x))
    · funext y
      simpa using congrFun h (cut.symm (Sum.inr y))
  · rintro ⟨rfl, rfl⟩
    funext v
    cases cut v <;> rfl

/-- The actual coefficient matrix is a sum of `d` products of the displayed unit vectors. -/
theorem ghzCoefficientMatrix_expansion {V A B : Type*} [Nonempty A]
    (cut : V ≃ A ⊕ B) (d : ℕ) (a : A → Fin d) (b : B → Fin d) :
    ghzCoefficientMatrix cut d a b =
      ∑ i : Fin d, (ghzSchmidtCoefficient d : ℂ) *
        ghzSchmidtVector A d i a * ghzSchmidtVector B d i b := by
  classical
  letI : Nonempty V := ⟨cut.symm (Sum.inl (Classical.choice (inferInstance : Nonempty A)))⟩
  rw [ghzCoefficientMatrix, ghzState_eq_finitePushforward]
  unfold finitePushforward
  apply Finset.sum_congr rfl
  intro i _
  have hi : (fun _ : V => i) = (fun v => Sum.elim a b (cut v)) ↔
      a = (fun _ => i) ∧ b = (fun _ => i) := by
    rw [eq_comm]
    exact joined_constant_iff cut a b i
  rw [hi]
  by_cases ha : a = (fun _ => i) <;> by_cases hb : b = (fun _ => i) <;>
    simp [ghzSchmidtVector_apply, ha, hb]

/-- The same decomposition written directly on the original path-label strings. -/
theorem ghzState_schmidt_expansion {V A B : Type*} [Nonempty A]
    (cut : V ≃ A ⊕ B) (d : ℕ) (s : V → Fin d) :
    ghzState V d s =
      ∑ i : Fin d, (ghzSchmidtCoefficient d : ℂ) *
        ghzSchmidtVector A d i (fun a => s (cut.symm (Sum.inl a))) *
        ghzSchmidtVector B d i (fun b => s (cut.symm (Sum.inr b))) := by
  have hj : (fun v => Sum.elim (fun a => s (cut.symm (Sum.inl a)))
      (fun b => s (cut.symm (Sum.inr b))) (cut v)) = s := by
    funext v
    calc
      _ = s (cut.symm (cut v)) := by cases cut v <;> rfl
      _ = s v := by rw [cut.symm_apply_apply]
  have h := ghzCoefficientMatrix_expansion cut d
    (fun a => s (cut.symm (Sum.inl a))) (fun b => s (cut.symm (Sum.inr b)))
  simpa only [ghzCoefficientMatrix, hj] using h

/--
Across every finite nonempty bipartition, the displayed expression is a
Schmidt decomposition with exactly `d` equal, positive coefficients. Both
orthonormality assertions use Mathlib's ordinary complex inner product.
-/
theorem ghz_schmidt_decomposition {V A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] [Nonempty A] [Nonempty B]
    (cut : V ≃ A ⊕ B) {d : ℕ} (hd : 0 < d) :
    Orthonormal ℂ (ghzSchmidtVector A d) ∧
    Orthonormal ℂ (ghzSchmidtVector B d) ∧
    0 < ghzSchmidtCoefficient d ∧
    (∑ _i : Fin d, ghzSchmidtCoefficient d ^ 2) = 1 ∧
    (∀ a b, ghzCoefficientMatrix cut d a b =
      ∑ i : Fin d, (ghzSchmidtCoefficient d : ℂ) *
        ghzSchmidtVector A d i a * ghzSchmidtVector B d i b) :=
  ⟨ghzSchmidtVector_orthonormal A d, ghzSchmidtVector_orthonormal B d,
    ghzSchmidtCoefficient_pos hd, ghzSchmidtCoefficient_sum_sq hd,
    ghzCoefficientMatrix_expansion cut d⟩

/-- A subset/complement form, so every nontrivial cut of a finite path set is covered. -/
theorem ghz_schmidt_on_subset {V : Type*} [Fintype V] [DecidableEq V] (S : Set V)
    [DecidablePred (· ∈ S)] (hS : S.Nonempty) (hSc : Sᶜ.Nonempty)
    {d : ℕ} (hd : 0 < d) :
    Orthonormal ℂ (ghzSchmidtVector S d) ∧
    Orthonormal ℂ (ghzSchmidtVector (Sᶜ : Set V) d) ∧
    0 < ghzSchmidtCoefficient d ∧
    (∑ _i : Fin d, ghzSchmidtCoefficient d ^ 2) = 1 ∧
    (∀ s : V → Fin d, ghzState V d s =
      ∑ i : Fin d, (ghzSchmidtCoefficient d : ℂ) *
        ghzSchmidtVector S d i (fun a => s a.1) *
        ghzSchmidtVector (Sᶜ : Set V) d i (fun b => s b.1)) := by
  classical
  letI : Nonempty S := hS.to_subtype
  letI : Nonempty (Sᶜ : Set V) := hSc.to_subtype
  refine ⟨ghzSchmidtVector_orthonormal S d,
    ghzSchmidtVector_orthonormal (Sᶜ : Set V) d,
    ghzSchmidtCoefficient_pos hd, ghzSchmidtCoefficient_sum_sq hd, ?_⟩
  intro s
  simpa using ghzState_schmidt_expansion (Equiv.Set.sumCompl S).symm d s

end RigidGHZ.SourceModel
