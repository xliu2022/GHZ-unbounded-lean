module

public import RigidGHZ.UpperBounds.Corollaries

/-! The small-part-size consequence `g_r(3) ≤ 2 * 3^(r-2)` in Section 4,
stated for every ordinary balanced rigid hypergraph. -/

@[expose] public section

namespace RigidGHZ.UpperBounds

theorem balanced_three_upper {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r d : ℕ} (hr : 2 ≤ r)
    (hR : IsRigid H d) (hP : BalancedPartite H r 3) :
    d ≤ 2 * 3 ^ (r - 2) := by
  have h := balanced_partite_harmonic_bound hr hR hP
  rw [beta_three] at h
  norm_num only [Nat.cast_ofNat] at h
  have hp : (3 : ℝ) ^ (r - 1) = 3 * (3 : ℝ) ^ (r - 2) := by
    rw [show r - 1 = (r - 2) + 1 by omega, pow_succ]
    ring
  rw [hp] at h
  have hd : (d : ℝ) ≤ 2 * (3 : ℝ) ^ (r - 2) := by linarith
  exact_mod_cast hd

end RigidGHZ.UpperBounds
