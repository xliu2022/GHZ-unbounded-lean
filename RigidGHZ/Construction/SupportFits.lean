module

public import RigidGHZ.Construction.RectangleAsymptotics

/-! The exact asymptotic support proportion is strictly below the packing limit. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology Rectangular

 theorem support_constant_lt_one {k : ℕ} (hk : 1 ≤ k) :
    (83 / 96 : ℝ) + 23 / (192 * (k : ℝ)) < 1 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hp : 0 < 192 * (k : ℝ) := by positivity
  have h : (23 : ℝ) / (192 * (k : ℝ)) < 1 - 83 / 96 := by
    apply (div_lt_iff₀ hp).mpr
    nlinarith
  linarith

 theorem exact_support_eventually_fits {k : ℕ} (hk : 1 ≤ k) {m u : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T)
    (hl : Tendsto (fun T => (k : ℝ) * u T / m T) atTop
      (𝓝 ((83 / 96 : ℝ) + 23 / (192 * (k : ℝ))))) :
    ∀ᶠ T in atTop, k * u T < m T := by
  have hb : ∀ᶠ T in atTop, (k : ℝ) * u T / m T < 1 :=
    hl.eventually (gt_mem_nhds (support_constant_lt_one hk))
  filter_upwards [hb, hw, eventually_ge_atTop 1] with T hb hw hT
  have hm : 0 < m T := by
    have hp : 0 < 128 * k ^ 3 * T ^ 7 := by positivity
    omega
  have hm' : (0 : ℝ) < m T := by exact_mod_cast hm
  have hprod := (div_lt_iff₀ hm').mp hb
  have hreal : (k : ℝ) * u T < m T := by simpa only [one_mul] using hprod
  exact_mod_cast hreal

 theorem rectangular_sequence_with_strict_support {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    ∃ G : ∀ T, Hypergraph (Fin 3 × Fin (m T)), ∃ U : ∀ T, Finset (Fin (m T)), ∃ R : ℕ → ℕ,
      (∀ᶠ T in atTop, ExactFactorWitness k T (m T) (G T) (U T) (R T) ∧ k * (U T).card < m T) ∧
      Tendsto (fun T => (k : ℝ) * (U T).card / m T) atTop
        (𝓝 ((83 / 96 : ℝ) + 23 / (192 * (k : ℝ)))) := by
  obtain ⟨G, U, R, he, hl⟩ := rectangular_sequence_with_support_limit hk hw
  have hb := exact_support_eventually_fits hk (hw.mono (fun _ h => h.1)) hl
  exact ⟨G, U, R, he.and hb, hl⟩

end RigidGHZ.RectangleAsymptotics
