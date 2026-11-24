module

public import RigidGHZ.Construction.MainGrowth
public import RigidGHZ.Construction.PrescribedSize

/-! Corollary 3.2: exactly the requested number of branches and source configurations. -/

@[expose] public section

namespace RigidGHZ.Growth

theorem prescribed_dimension_shifted {k d m : ℕ} (hk : 1 ≤ k) (hd : 2 ≤ d)
    (hsize : prescribedSize k d ≤ m) :
    ∃ H : Hypergraph (Fin (k + 2) × Fin m),
      Uniform H (k + 2) ∧ BalancedPartite H (k + 2) m ∧ IsRigid H d ∧ H.card = d * m := by
  have hmpos := (prescribedSize_pos hk (show 1 ≤ d by omega)).trans_le hsize
  have hm : 1 ≤ m := hmpos
  obtain ⟨D, hD, hgrowth⟩ := balanced_growth_shifted hk hm
  have hrequested := prescribedSize_suffices hk (show 1 ≤ d by omega) hsize
  have hdD : d ≤ D := by exact_mod_cast hrequested.trans hgrowth
  obtain ⟨H, hU, hP, ⟨R⟩⟩ := hD.restrict (by omega) hm hdD
  refine ⟨H, hU, hP, ⟨R⟩, ?_⟩
  simpa only [Fintype.card_fin] using R.card_edges hU (by omega) (by simp)

/-- Any part size at least the explicit ceiling supports exactly `d` branches. -/
theorem prescribed_dimension_at_least (r d m : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d)
    (hsize : prescribedSize (r - 2) d ≤ m) :
    ∃ H : Hypergraph (Fin r × Fin m),
      Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H d ∧ H.card = d * m := by
  generalize hk : r - 2 = k at hsize
  have hrk : r = k + 2 := by omega
  subst r
  exact prescribed_dimension_shifted (by omega) hd hsize

/-- The exact part size stated in Corollary 3.2. -/
theorem prescribed_dimension (r d : ℕ) (hr : 3 ≤ r) (hd : 2 ≤ d) :
    ∃ H : Hypergraph (Fin r × Fin (prescribedSize (r - 2) d)),
      Uniform H r ∧ BalancedPartite H r (prescribedSize (r - 2) d) ∧
      IsRigid H d ∧ H.card = d * prescribedSize (r - 2) d :=
  prescribed_dimension_at_least r d _ hr hd le_rfl

end RigidGHZ.Growth
