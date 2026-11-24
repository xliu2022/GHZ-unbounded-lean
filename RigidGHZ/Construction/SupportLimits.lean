module

public import RigidGHZ.Construction.OwnerMassLimits
public import RigidGHZ.Construction.ExactRectangularFactor

/-! Exact asymptotic active-support proportion of the constructed hypergraphs. -/

@[expose] public section

noncomputable section

set_option maxHeartbeats 3000000

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology RectangleEstimates Rectangular

 theorem supportCount_ratio {k : ℕ} (hk : 1 ≤ k) {m R : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7)
    (hR : ∀ᶠ T in atTop, (R T : ℝ) =
      privateAmount k T (boxHeight k T (m T)) (remainder k T (m T))) :
    RatioLimit (fun T => (supportCount k T (boxHeight k T (m T)) (R T) : ℝ)) 7
      ((332 / 3 : ℝ) * (k : ℝ) ^ 2 + (46 / 3 : ℝ) * k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hheight := box_height_eventual hk hw
  have hlower := hheight.mono (fun _ h => h.1)
  have hH := box_height_ratio hk hw
  have hO := ownerMass_ratio hk' hH hlower
  have hr : RatioLimit (fun T => (R T : ℝ)) 5 ((46 / 3 : ℝ) * k) :=
    (privateAmount_ratio hk' hheight (remainder_bounds_eventual hk m)).congr (hR.mono (fun _ h => h.symm))
  have hp : RatioLimit (fun T => (T : ℝ) + 1) 1 1 := by
    simpa using ratio_variable.add (ratio_const 1 (by omega : 0 < 1))
  have htotal : RatioLimit (fun T => 1 + ((T : ℝ) + 1) * ownerMass k T (boxHeight k T (m T)) +
      ((T : ℝ) + 1) ^ 2 * R T) 7 ((332 / 3 : ℝ) * (k : ℝ) ^ 2 + (46 / 3 : ℝ) * k) := by
    simpa using ((ratio_const 1 (by omega : 0 < 7)).add (hp.mul hO)).add ((hp.pow 2).mul hr)
  apply htotal.congr
  filter_upwards [hlower, eventually_ge_atTop 6] with T hH hT
  exact (supportCount_cast k T (boxHeight k T (m T)) (R T) hk hT hH).symm

/-- The asymptotic constant counts actual support vertices, not a containing
box or an upper envelope. -/
theorem support_fraction_of_exact_counts {k : ℕ} (hk : 1 ≤ k) {m R u : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7)
    (hR : ∀ᶠ T in atTop, (R T : ℝ) =
      privateAmount k T (boxHeight k T (m T)) (remainder k T (m T)))
    (hu : ∀ᶠ T in atTop, u T = supportCount k T (boxHeight k T (m T)) (R T)) :
    Tendsto (fun T => (k : ℝ) * u T / m T) atTop
      (𝓝 ((83 / 96 : ℝ) + 23 / (192 * (k : ℝ)))) := by
  have hU : RatioLimit (fun T => (u T : ℝ)) 7
      ((332 / 3 : ℝ) * (k : ℝ) ^ 2 + (46 / 3 : ℝ) * k) := by
    apply (supportCount_ratio hk hw hR).congr
    filter_upwards [hu] with T hT
    exact congrArg (fun x : ℕ => (x : ℝ)) hT.symm
  have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hm0 : 128 * (k : ℝ) ^ 3 ≠ 0 := by positivity
  have h := RatioLimit.div (n := 0) (hU.const_mul (k : ℝ)) (size_ratio hk hw) hm0
  have he : ((k : ℝ) * ((332 / 3 : ℝ) * (k : ℝ) ^ 2 + (46 / 3 : ℝ) * k)) /
      (128 * (k : ℝ) ^ 3) = (83 / 96 : ℝ) + 23 / (192 * (k : ℝ)) := by
    field_simp
    ring
  simpa only [RatioLimit, pow_zero, div_one, he] using h

/-- For every sequence of allowed input sizes, there is a sequence of ordinary
rigid hypergraphs whose exact active supports have the claimed limit. All
matching and support assertions come from the actual geometric construction. -/
theorem rectangular_sequence_with_support_limit {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    ∃ G : ∀ T, Hypergraph (Fin 3 × Fin (m T)), ∃ U : ∀ T, Finset (Fin (m T)), ∃ R : ℕ → ℕ,
      (∀ᶠ T in atTop, ExactFactorWitness k T (m T) (G T) (U T) (R T)) ∧
      Tendsto (fun T => (k : ℝ) * (U T).card / m T) atTop
        (𝓝 ((83 / 96 : ℝ) + 23 / (192 * (k : ℝ)))) := by
  classical
  have hex : ∀ T, ∃ G : Hypergraph (Fin 3 × Fin (m T)), ∃ U : Finset (Fin (m T)), ∃ R : ℕ,
      (224 ≤ T ∧ 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) →
        ExactFactorWitness k T (m T) G U R := by
    intro T
    by_cases h : 224 ≤ T ∧ 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7
    · obtain ⟨G, U, R, hR⟩ := exact_rectangular_factor hk h.1 h.2.1 h.2.2
      exact ⟨G, U, R, fun _ => hR⟩
    · exact ⟨∅, ∅, 0, fun hh => (h hh).elim⟩
  choose G U R hspec using hex
  have he : ∀ᶠ T in atTop, ExactFactorWitness k T (m T) (G T) (U T) (R T) := by
    filter_upwards [hw, eventually_ge_atTop 224] with T hw hT
    exact hspec T ⟨hT, hw⟩
  refine ⟨G, U, R, he, support_fraction_of_exact_counts (R := R) hk hw ?_ ?_⟩
  · exact he.mono (fun T h => h.2.2.2.2.2.1)
  · exact he.mono (fun T h => h.2.2.2.2.2.2)

 theorem rectangular_sequence_support_one {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * T ^ 7 ≤ m T ∧ m T < 128 * (T + 1) ^ 7) :
    ∃ G : ∀ T, Hypergraph (Fin 3 × Fin (m T)), ∃ U : ∀ T, Finset (Fin (m T)), ∃ R : ℕ → ℕ,
      (∀ᶠ T in atTop, ExactFactorWitness 1 T (m T) (G T) (U T) (R T)) ∧
      Tendsto (fun T => ((U T).card : ℝ) / m T) atTop (𝓝 (63 / 64 : ℝ)) := by
  have hw' : ∀ᶠ T in atTop, 128 * 1 ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * 1 ^ 3 * (T + 1) ^ 7 := by
    simpa using hw
  obtain ⟨G, U, R, he, hl⟩ := rectangular_sequence_with_support_limit (k := 1) (by omega) hw'
  refine ⟨G, U, R, he, ?_⟩
  norm_num at hl ⊢
  exact hl

end RigidGHZ.RectangleAsymptotics
