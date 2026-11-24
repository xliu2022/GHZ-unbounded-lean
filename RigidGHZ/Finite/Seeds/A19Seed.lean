module

public import RigidGHZ.Finite.Seeds.A19
public import RigidGHZ.Finite.Seeds.A19Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A19
open RigidGHZ.Supplement.Affine

theorem seed : Seed (3 : ZMod 19) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 3 19).mpr (by decide)
  unit_right := by
    change IsUnit (4 : ZMod 19)
    exact (ZMod.isUnit_iff_coprime 4 19).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A19
