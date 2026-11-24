module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.GraftDegrees

/-! Codegrees of an injectively indexed edge table are index counts. -/
@[expose] public section
namespace RigidGHZ.Finite
open RigidGHZ.UpperBounds

 theorem exactCover_codegree_of_indices {V : Type*} [DecidableEq V]
    {n e d : ℕ} (D : ExactCoverData V n e d)
    (hinj : Function.Injective D.edge) (X : Finset V) :
    codegree D.host X =
      ((Finset.univ : Finset (Fin e)).filter (fun i => X ⊆ D.edge i)).card := by
  rw [codegree, ExactCoverData.host, Finset.filter_image,
    Finset.card_image_of_injective _ hinj]

end RigidGHZ.Finite
