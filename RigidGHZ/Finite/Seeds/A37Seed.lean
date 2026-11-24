module

public import RigidGHZ.Finite.Seeds.A37
public import RigidGHZ.Finite.Seeds.A37Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A37
open RigidGHZ.Supplement.Affine

theorem seed : Seed (1 : ZMod 37) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 1 37).mpr (by decide)
  unit_right := by
    change IsUnit (2 : ZMod 37)
    exact (ZMod.isUnit_iff_coprime 2 37).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A37
