module

public import RigidGHZ.Construction.SupportLimits

/-! All construction constants in the closing paragraph of Appendix A,
for the actual sequence of rigid hypergraphs and exact active supports. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleAsymptotics

open Filter Topology RectangleEstimates Rectangular

 theorem rectangular_asymptotic_constants {k : ℕ} (hk : 1 ≤ k) {m : ℕ → ℕ}
    (hw : ∀ᶠ T in atTop, 128 * k ^ 3 * T ^ 7 ≤ m T ∧ m T < 128 * k ^ 3 * (T + 1) ^ 7) :
    ∃ G : ∀ T, Hypergraph (Fin 3 × Fin (m T)), ∃ U : ∀ T, Finset (Fin (m T)), ∃ R : ℕ → ℕ,
      (∀ᶠ T in atTop, ExactFactorWitness k T (m T) (G T) (U T) (R T)) ∧
      RatioLimit (fun T => (m T : ℝ)) 7 (128 * (k : ℝ) ^ 3) ∧
      RatioLimit (fun T => (boxHeight k T (m T) : ℝ)) 3 ((16 / 3 : ℝ) * k) ∧
      RatioLimit (fun T => (nHorizontal k T (boxHeight k T (m T)) : ℝ)) 2 (4 * k) ∧
      RatioLimit (fun T => (nVertical k T (boxHeight k T (m T)) : ℝ)) 2 (4 * k) ∧
      RatioLimit (fun T => (nFull k T (boxHeight k T (m T)) : ℝ)) 1 (11 / 8) ∧
      RatioLimit (fun T => (R T : ℝ)) 5 ((46 / 3 : ℝ) * k) ∧
      Tendsto (fun T => (k : ℝ) * (U T).card / m T) atTop
        (𝓝 ((83 / 96 : ℝ) + 23 / (192 * (k : ℝ)))) := by
  obtain ⟨G, U, R, he, hsupport⟩ := rectangular_sequence_with_support_limit hk hw
  have hH := box_height_ratio hk hw
  have hheight := box_height_eventual hk hw
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hcounts := rounded_counts_ratio hk' hH (hheight.mono (fun _ h => h.1))
  have hR : RatioLimit (fun T => (R T : ℝ)) 5 ((46 / 3 : ℝ) * k) := by
    apply (privateAmount_ratio hk' hheight (remainder_bounds_eventual hk m)).congr
    filter_upwards [he] with T he
    exact he.2.2.2.2.2.1.symm
  exact ⟨G, U, R, he, size_ratio hk hw, hH, hcounts.1, hcounts.2.1, hcounts.2.2, hR, hsupport⟩

end RigidGHZ.RectangleAsymptotics
