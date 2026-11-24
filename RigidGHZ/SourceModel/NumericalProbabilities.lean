module

public import RigidGHZ.SourceModel.SuccessAsymptotics

/-! Rational interval certificates for the five three-significant-figure
probabilities printed in Section 5.  All endpoints are exact rationals. -/

@[expose] public section

namespace RigidGHZ.SourceModel

set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

theorem optimal_3_12_rounding :
    (785 : ℝ) / (2 * 10 ^ 6) ≤ optimalProbability 3 12 ∧
      optimalProbability 3 12 < (787 : ℝ) / (2 * 10 ^ 6) := by
  norm_num [optimalProbability]

theorem optimal_13_12_rounding :
    (885 : ℝ) / (2 * 10 ^ 21) ≤ optimalProbability 13 12 ∧
      optimalProbability 13 12 < (887 : ℝ) / (2 * 10 ^ 21) := by
  norm_num [optimalProbability]

theorem optimal_39_12_rounding :
    (1203 : ℝ) / (2 * 10 ^ 60) ≤ optimalProbability 39 12 ∧
      optimalProbability 39 12 < (1205 : ℝ) / (2 * 10 ^ 60) := by
  norm_num [optimalProbability]
  rw [show (429 : ℕ) = 200 + 229 from rfl, pow_add]
  norm_num

theorem optimal_3_13_rounding :
    (663 : ℝ) / (2 * 10 ^ 6) ≤ optimalProbability 3 13 ∧
      optimalProbability 3 13 < (665 : ℝ) / (2 * 10 ^ 6) := by
  norm_num [optimalProbability]

theorem optimal_6_13_rounding :
    (1691 : ℝ) / (2 * 10 ^ 11) ≤ optimalProbability 6 13 ∧
      optimalProbability 6 13 < (1693 : ℝ) / (2 * 10 ^ 11) := by
  norm_num [optimalProbability]

end RigidGHZ.SourceModel
