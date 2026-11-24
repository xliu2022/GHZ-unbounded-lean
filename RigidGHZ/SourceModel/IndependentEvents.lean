module

public import RigidGHZ.SourceModel.JointState
public import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! Finite independent Bernoulli weights, the actual expected number of
emitting sources, and independent flagged detection of all selected photons. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

section Bernoulli

variable {α : Type*} [DecidableEq α]

def independentWeight (A : Finset α) (p : α → ℝ) (S : Finset α) : ℝ :=
  (∏ e ∈ S, p e) * ∏ e ∈ A \ S, (1 - p e)

theorem independentWeight_nonneg (A : Finset α) (p : α → ℝ)
    (hp : ∀ e ∈ A, 0 ≤ p e ∧ p e ≤ 1) {S : Finset α} (hS : S ⊆ A) :
    0 ≤ independentWeight A p S := by
  apply mul_nonneg
  · exact Finset.prod_nonneg (fun e he => (hp e (hS he)).1)
  · exact Finset.prod_nonneg (fun e he => sub_nonneg.mpr (hp e (Finset.mem_sdiff.mp he).1).2)

theorem independentWeight_sum (A : Finset α) (p : α → ℝ) :
    ∑ S ∈ A.powerset, independentWeight A p S = 1 := by
  simp_rw [independentWeight]
  rw [← Finset.prod_add]
  simp

theorem independentWeight_insert_absent (A : Finset α) (p : α → ℝ) {a : α}
    (ha : a ∉ A) {S : Finset α} (hS : S ⊆ A) :
    independentWeight (insert a A) p S = (1 - p a) * independentWeight A p S := by
  have haS : a ∉ S := fun h => ha (hS h)
  simp [independentWeight, Finset.insert_sdiff_of_notMem, haS, ha, mul_left_comm]

theorem independentWeight_insert_present (A : Finset α) (p : α → ℝ) {a : α}
    (ha : a ∉ A) {S : Finset α} (hS : S ⊆ A) :
    independentWeight (insert a A) p (insert a S) = p a * independentWeight A p S := by
  have haS : a ∉ S := fun h => ha (hS h)
  have hs : insert a A \ insert a S = A \ S := by ext x; simp; aesop
  simp [independentWeight, hs, haS, mul_assoc]

/-- The first moment of the independent distribution, proved as a finite sum. -/
theorem independentWeight_expected_card (A : Finset α) (p : α → ℝ) :
    ∑ S ∈ A.powerset, (S.card : ℝ) * independentWeight A p S = ∑ e ∈ A, p e := by
  induction A using Finset.induction_on with
  | empty => simp [independentWeight]
  | @insert a A ha ih =>
    rw [Finset.sum_powerset_insert ha]
    have hfirst :
        (∑ S ∈ A.powerset, (S.card : ℝ) * independentWeight (insert a A) p S) =
          (1 - p a) * ∑ S ∈ A.powerset, (S.card : ℝ) * independentWeight A p S := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      rw [independentWeight_insert_absent A p ha (Finset.mem_powerset.mp hS)]
      ring
    have hsecond :
        (∑ S ∈ A.powerset, ((insert a S).card : ℝ) *
          independentWeight (insert a A) p (insert a S)) =
          p a * ((∑ S ∈ A.powerset, (S.card : ℝ) * independentWeight A p S) + 1) := by
      rw [← independentWeight_sum A p, ← Finset.sum_add_distrib, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro S hS
      have hs := Finset.mem_powerset.mp hS
      have haS : a ∉ S := fun h => ha (hs h)
      rw [independentWeight_insert_present A p ha hs, Finset.card_insert_of_notMem haS]
      push_cast
      ring
    rw [hfirst, hsecond, ih, Finset.sum_insert ha]
    ring

end Bernoulli

variable {V I : Type*} [DecidableEq V] {H : Hypergraph V}

def expectedEmissions (p φ : Finset V → ℝ) : ℝ :=
  ∑ S : EmissionPattern H, (S.val.card : ℝ) * Complex.normSq (patternAmplitude p φ S)

theorem expectedEmissions_eq (p φ : Finset V → ℝ)
    (hp : ∀ e ∈ H, 0 ≤ p e ∧ p e ≤ 1) :
    expectedEmissions (H := H) p φ = ∑ e ∈ H, p e := by
  unfold expectedEmissions
  simp_rw [patternAmplitude_normSq p φ hp]
  calc
    _ = ∑ S : ↥H.powerset, (S.val.card : ℝ) * independentWeight H p S.val :=
      (emissionPatternEquiv H).sum_comp _
    _ = ∑ S ∈ H.powerset, (S.card : ℝ) * independentWeight H p S :=
      Finset.sum_coe_sort H.powerset
        (fun S : Hypergraph V => (S.card : ℝ) * independentWeight H p S)
    _ = _ := independentWeight_expected_card H p

/-- At the optimal pump the expected number of emitting sources is `m`. -/
theorem expectedEmissions_optimal [Fintype V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hU : Uniform H r) (hr : 0 < r) (hd : 1 ≤ d)
    (hV : Fintype.card V = r * m) (φ : Finset V → ℝ) :
    expectedEmissions (H := H) (fun _ => 1 / (d : ℝ)) φ = m := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  rw [expectedEmissions_eq _ _ (fun e he => ⟨by positivity,
    (div_le_one hd0).mpr (by exact_mod_cast hd)⟩)]
  have hc := G.card_edges hU hr hV
  simp only [Finset.sum_const, nsmul_eq_mul, hc, Fintype.card_fin, Nat.cast_mul]
  field_simp

def expectedPhotons (r : ℕ) (p φ : Finset V → ℝ) : ℝ :=
  ∑ S : EmissionPattern H, (r * S.val.card : ℝ) * Complex.normSq (patternAmplitude p φ S)

/-- Each source emits `r` photons, so the optimum has expected total `r*m`. -/
theorem expectedPhotons_optimal [Fintype V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hU : Uniform H r) (hr : 0 < r) (hd : 1 ≤ d)
    (hV : Fintype.card V = r * m) (φ : Finset V → ℝ) :
    expectedPhotons (H := H) r (fun _ => 1 / (d : ℝ)) φ = (r * m : ℕ) := by
  simp only [expectedPhotons, mul_assoc, ← Finset.mul_sum]
  change (r : ℝ) * expectedEmissions (H := H) (fun _ => 1 / (d : ℝ)) φ = _
  rw [expectedEmissions_optimal G hU hr hd hV φ]
  push_cast
  rfl

/-- The path/label modes are the ordinary Cartesian product. -/
theorem mode_count [Fintype V] [Fintype I] :
    Fintype.card (V × I) = Fintype.card V * Fintype.card I := Fintype.card_prod V I

/-- Independent transmission/detection outcomes on the already selected paths. -/
def detectionWeight [Fintype V] (η : ℝ) (detected : Finset V) : ℝ :=
  independentWeight Finset.univ (fun _ : V => η) detected

theorem detectionWeight_sum [Fintype V] (η : ℝ) :
    ∑ D ∈ (Finset.univ : Finset V).powerset, detectionWeight η D = 1 :=
  independentWeight_sum _ _

theorem detectionWeight_all [Fintype V] (η : ℝ) :
    detectionWeight η (Finset.univ : Finset V) = η ^ Fintype.card V := by
  simp [detectionWeight, independentWeight]

/-- Joint probability of an ideal accepted matching and all photons detected.
The product explicitly expresses independence and therefore models flagged
loss or loss after the ideal selection. -/
def flaggedDetectionProbability [Fintype V] (b : PerfectMatchings H → ℂ) (η : ℝ) : ℝ :=
  ∑ M, Complex.normSq (b M) * detectionWeight η (Finset.univ : Finset V)

theorem flaggedDetectionProbability_eq [Fintype V] [Fintype I]
    (F : MatchingDecomposition H I) (hn : ∀ e ∈ H, e.Nonempty)
    (b : PerfectMatchings H → ℂ) (η : ℝ) :
    flaggedDetectionProbability b η = η ^ Fintype.card V * stateNormSq (F.acceptedState b) := by
  rw [acceptedState_normSq F hn, flaggedDetectionProbability]
  simp_rw [detectionWeight_all]
  rw [← Finset.sum_mul, mul_comm]

end RigidGHZ.SourceModel
