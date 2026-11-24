module

public import RigidGHZ.Supplement.Periodic.Ten
public import RigidGHZ.Supplement.Periodic.TraceCertificates

/-! The two-cycle has weights two and one; its even-period contribution is exact. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Ten

 theorem xy_valid : ∀ A ∈ xyConfigurations, scheme.LocalConfig A := by
  intro A hA
  simp only [xyConfigurations, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl | rfl
  all_goals decide

 theorem yx_valid : ∀ A ∈ yxConfigurations, scheme.LocalConfig A := by
  intro A hA
  simp only [yxConfigurations, Finset.mem_singleton] at hA
  subst A
  decide

 theorem xy_weight : scheme.transferMatrix ∅ Finset.univ = 2 := by
  rw [scheme.transferMatrix_eq_catalog ∅ Finset.univ xyConfigurations xy_valid
    (fun A hA => (certificate hA).2.2.2.1)]
  decide

 theorem yx_weight : scheme.transferMatrix Finset.univ ∅ = 1 := by
  rw [scheme.transferMatrix_eq_catalog Finset.univ ∅ yxConfigurations yx_valid
    (fun A hA => (certificate hA).2.2.2.2)]
  decide

 theorem trace_formula {q : ℕ} (hq : 0 < q) :
    Matrix.trace (scheme.transferMatrix ^ q) = 10 +
      if Even q then 2 * 2 ^ (q / 2) else 0 := by
  have hloops := fun A hA => (certificate (A := A) hA).2.2.1
  have htrace : Matrix.trace scheme.transferMatrix = 10 := by
    simpa using scheme.trace_eq_classes color classes_local classes_loop class_inputs_injective hloops
  have hmono := scheme.blockTriangular_of_monotone height (fun A hA => (certificate hA).1)
  have hflat := scheme.exceptional_flat_zero height ∅ Finset.univ
    (fun A hA => (certificate hA).2.1)
  have hx0 := scheme.diagonal_zero color hloops ∅ (fun i => (class_inputs_avoid i).1)
  have hy0 := scheme.diagonal_zero color hloops Finset.univ (fun i => (class_inputs_avoid i).2)
  have hdiag := scheme.diagonal_le_one color class_inputs_injective hloops
  have h := MatrixHeight.exceptional_trace scheme.transferMatrix height ∅ Finset.univ
    (by decide) (by decide) hmono hflat hx0 hy0 hdiag hq
  simpa only [htrace, xy_weight, yx_weight, Nat.mul_one] using h

 theorem perfectMatching_count {q : ℕ} (hq : 0 < q) :
    Fintype.card {M : Hypergraph (Fin 6 × Fin q) //
      PerfectMatching (scheme.graph (finRotate q)) M} = 10 +
      if Even q then 2 * 2 ^ (q / 2) else 0 := by
  rw [scheme.perfectMatching_count_eq_trace hq, trace_formula hq]

end RigidGHZ.Supplement.Periodic.Ten
