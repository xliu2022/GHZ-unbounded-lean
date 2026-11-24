module

public import RigidGHZ.Finite.Seeds.A31
public import RigidGHZ.Finite.Seeds.A31Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A31
open RigidGHZ.Supplement.Affine

theorem seed : Seed (4 : ZMod 31) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 4 31).mpr (by decide)
  unit_right := by
    change IsUnit (5 : ZMod 31)
    exact (ZMod.isUnit_iff_coprime 5 31).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A31
