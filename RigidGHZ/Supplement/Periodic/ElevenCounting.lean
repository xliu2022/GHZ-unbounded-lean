module

public import RigidGHZ.Supplement.Periodic.Eleven
public import RigidGHZ.Supplement.Periodic.TraceCertificates

/-! Exact transfer trace and actual perfect-matching counts for every period. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Eleven

 theorem trace_formula {q : ℕ} (hq : 0 < q) : Matrix.trace (scheme.transferMatrix ^ q) = 11 := by
  have hmono : scheme.transferMatrix.BlockTriangular height :=
    scheme.blockTriangular_of_monotone height (fun A hA => by
      rcases (certificate hA).1 with h | h
      · rw [h]
      · exact h.le)
  have hflat := scheme.strict_flat_zero height (fun A hA => (certificate hA).1)
  have hdiag := scheme.diagonal_le_one color class_inputs_injective
    (fun A hA => (certificate hA).2)
  rw [MatrixHeight.strict_trace scheme.transferMatrix height hmono hflat hdiag hq]
  simpa using scheme.trace_eq_classes color classes_local classes_loop class_inputs_injective
    (fun A hA => (certificate hA).2)

 theorem perfectMatching_count {q : ℕ} (hq : 0 < q) :
    Fintype.card {M : Hypergraph (Fin 9 × Fin q) //
      PerfectMatching (scheme.graph (finRotate q)) M} = 11 := by
  rw [scheme.perfectMatching_count_eq_trace hq, trace_formula hq]

end RigidGHZ.Supplement.Periodic.Eleven
