module

public import RigidGHZ.Supplement.Periodic.ElevenFamily
public import RigidGHZ.Supplement.Periodic.Ten
public import RigidGHZ.Supplement.Periodic.Latin

/-! The three infinite periodic families, as canonical ordinary hypergraphs. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic

 theorem ten_bounded {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    BoundedUnrestricted 3 (2 * q) 10 (fun _ => 10) := by
  let e : Fin 6 × Fin q ≃ Fin (3 * (2 * q)) :=
    finProdFinEquiv.trans (finCongr (by omega))
  let H := relabelHypergraph e (Ten.scheme.graph (finRotate q))
  have hR : IsRigid H 10 := IsRigid.relabel ⟨Ten.rigidFamily hq hodd⟩ e
  exact ⟨H, (Ten.uniform q).relabel e, hR, fun j hj => maxDegree_rigid_le hR hj⟩

 theorem ten_ten : BoundedUnrestricted 3 10 10 (fun _ => 10) := by
  simpa using ten_bounded (by decide : 0 < 5) (by decide : Odd 5)

 theorem latin_bounded {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    BoundedRigid 3 (8 * q) 8 (pairBounds 8 1) :=
  boundedRigid_of_pair_bound (Latin.uniform q) (Latin.balanced q)
    ⟨Latin.rigidFamily hq hodd⟩ ((linear_iff_pair_bound _).mp (Latin.linear q))

end RigidGHZ.Supplement.Periodic
