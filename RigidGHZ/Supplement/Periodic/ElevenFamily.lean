module

public import RigidGHZ.Supplement.Periodic.Eleven
public import RigidGHZ.Supplement.GraftSemigroup

/-! Canonical witnesses for the unrestricted eleven-matching family. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic

 theorem eleven_bounded {q : ℕ} (hq : 0 < q) :
    BoundedUnrestricted 3 (3 * q) 11 (fun _ => 11) := by
  let e : Fin 9 × Fin q ≃ Fin (3 * (3 * q)) :=
    finProdFinEquiv.trans (finCongr (by omega))
  let H := relabelHypergraph e (Eleven.scheme.graph (finRotate q))
  have hR : IsRigid H 11 := IsRigid.relabel ⟨Eleven.rigidFamily hq⟩ e
  exact ⟨H, (Eleven.uniform q).relabel e, hR, fun j hj => maxDegree_rigid_le hR hj⟩

 theorem eleven_nine : BoundedUnrestricted 3 9 11 (fun _ => 11) := by
  simpa using eleven_bounded (by decide : 0 < 3)

end RigidGHZ.Supplement.Periodic
