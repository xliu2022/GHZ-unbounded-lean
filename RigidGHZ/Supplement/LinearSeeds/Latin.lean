module

public import RigidGHZ.Supplement.LinearSeedTools
public import RigidGHZ.Supplement.Periodic.Latin

/-! The one- and three-period Latin seeds used in the linear residue table. -/

@[expose] public section

namespace RigidGHZ.Supplement.LinearSeeds

 theorem q8 : LinearSeed 8 8 := by
  have h := boundedRigid_of_pair_bound (Periodic.Latin.uniform 1) (Periodic.Latin.balanced 1)
    (show IsRigid (Periodic.Latin.scheme.graph (finRotate 1)) 8 from
      ⟨Periodic.Latin.rigidFamily (by decide) (by decide)⟩)
    ((linear_iff_pair_bound _).mp (Periodic.Latin.linear 1))
  simpa using h

 theorem q24 : LinearSeed 24 8 := by
  have h := boundedRigid_of_pair_bound (Periodic.Latin.uniform 3) (Periodic.Latin.balanced 3)
    (show IsRigid (Periodic.Latin.scheme.graph (finRotate 3)) 8 from
      ⟨Periodic.Latin.rigidFamily (by decide) (by decide)⟩)
    ((linear_iff_pair_bound _).mp (Periodic.Latin.linear 3))
  simpa using h

end RigidGHZ.Supplement.LinearSeeds
