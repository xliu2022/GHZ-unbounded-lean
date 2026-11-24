module

public import RigidGHZ.Supplement.Periodic.Latin
public import RigidGHZ.Supplement.Periodic.TraceCertificates

/-! The Latin two-cycle has weights five and one, including all even-period
extra perfect matchings in the exact counting formula. -/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

namespace RigidGHZ.Supplement.Periodic.Latin

 theorem loop_complete (A : Finset (Fin 64)) (hA : scheme.LocalConfig A)
    (he : scheme.input A = scheme.output A) : ∃ i, A = colorClass color i := by
  obtain ⟨i, hi⟩ := (certificate hA).2.2.1 he
  exact ⟨i, hi.trans (classes_eq i).symm⟩

 theorem xy_valid : ∀ A ∈ xyConfigurations, scheme.LocalConfig A := by
  intro A hA
  simp only [xyConfigurations, Finset.mem_insert, Finset.mem_singleton] at hA
  rcases hA with rfl | rfl | rfl | rfl | rfl
  all_goals decide

 theorem yx_valid : ∀ A ∈ yxConfigurations, scheme.LocalConfig A := by
  intro A hA
  simp only [yxConfigurations, Finset.mem_singleton] at hA
  subst A
  decide

 theorem xy_weight : scheme.transferMatrix x y = 5 := by
  rw [scheme.transferMatrix_eq_catalog x y xyConfigurations xy_valid
    (fun A hA => (certificate hA).2.2.2.1)]
  decide

 theorem yx_weight : scheme.transferMatrix y x = 1 := by
  rw [scheme.transferMatrix_eq_catalog y x yxConfigurations yx_valid
    (fun A hA => (certificate hA).2.2.2.2)]
  decide

 theorem trace_formula {q : ℕ} (hq : 0 < q) :
    Matrix.trace (scheme.transferMatrix ^ q) = 8 +
      if Even q then 2 * 5 ^ (q / 2) else 0 := by
  have htrace : Matrix.trace scheme.transferMatrix = 8 := by
    simpa using scheme.trace_eq_classes color classes_local classes_loop class_inputs_injective loop_complete
  have hmono := scheme.blockTriangular_of_monotone height (fun A hA => (certificate hA).1)
  have hflat := scheme.exceptional_flat_zero height x y
    (fun A hA => (certificate hA).2.1)
  have hx0 := scheme.diagonal_zero color loop_complete x (fun i => (class_inputs_avoid i).1)
  have hy0 := scheme.diagonal_zero color loop_complete y (fun i => (class_inputs_avoid i).2)
  have hdiag := scheme.diagonal_le_one color class_inputs_injective loop_complete
  have h := MatrixHeight.exceptional_trace scheme.transferMatrix height x y
    (by decide) (by decide) hmono hflat hx0 hy0 hdiag hq
  simpa only [htrace, xy_weight, yx_weight, Nat.mul_one] using h

 theorem perfectMatching_count {q : ℕ} (hq : 0 < q) :
    Fintype.card {M : Hypergraph (Fin 24 × Fin q) //
      PerfectMatching (scheme.graph (finRotate q)) M} = 8 +
      if Even q then 2 * 5 ^ (q / 2) else 0 := by
  rw [scheme.perfectMatching_count_eq_trace hq, trace_formula hq]

end RigidGHZ.Supplement.Periodic.Latin
