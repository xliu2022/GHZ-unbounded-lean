module

public import RigidGHZ.Supplement.Periodic.TracePaths
public import RigidGHZ.Supplement.Periodic.Enumeration

/-! The exact transfer-matrix identity for ordinary perfect matchings. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

 abbrev Configurations := {A : Finset E // D.LocalConfig A}

instance : Fintype D.Configurations := inferInstanceAs (Fintype {A : Finset E // D.LocalConfig A})

noncomputable def transferMatrix : Matrix (Finset V) (Finset V) ℕ :=
  WeightedWalks.matrix (fun A : D.Configurations => D.input A.1)
    (fun A : D.Configurations => D.output A.1)

noncomputable instance (q : ℕ) : Fintype {A : Fin q → Finset E // D.PeriodicConfig (finRotate q) A} :=
  Fintype.ofFinite _

noncomputable instance (q : ℕ) :
    Fintype {M : Hypergraph (V × Fin q) // PerfectMatching (D.graph (finRotate q)) M} :=
  Fintype.ofFinite _

 def periodicConfigEquivWords (q : ℕ) :
    {A : Fin q → Finset E // D.PeriodicConfig (finRotate q) A} ≃
    WeightedWalks.ClosedWords (fun A : D.Configurations => D.input A.1)
      (fun A : D.Configurations => D.output A.1) q where
  toFun A := ⟨fun j => ⟨A.1 j, A.2.1 j⟩, A.2.2⟩
  invFun A := ⟨fun j => (A.1 j).1, ⟨fun j => (A.1 j).2, A.2⟩⟩
  left_inv A := by apply Subtype.ext; rfl
  right_inv A := by apply Subtype.ext; funext j; rfl

/-- Every multiplicity in the matrix counts a distinct actual local edge set.
The trace counts ordinary perfect matchings, including even-period extra ones. -/
theorem perfectMatching_count_eq_trace {q : ℕ} (hq : 0 < q) :
    Fintype.card {M : Hypergraph (V × Fin q) // PerfectMatching (D.graph (finRotate q)) M} =
      Matrix.trace (D.transferMatrix ^ q) := by
  rw [← Fintype.card_congr (D.configEquivMatching (finRotate q)),
    Fintype.card_congr (D.periodicConfigEquivWords q)]
  exact WeightedWalks.closed_card_trace _ _ hq

end RigidGHZ.Supplement.Periodic.Scheme
