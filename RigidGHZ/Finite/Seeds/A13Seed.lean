module

public import RigidGHZ.Finite.Seeds.A13
public import RigidGHZ.Finite.Seeds.A13Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A13
open RigidGHZ.Supplement.Affine

theorem seed : Seed (2 : ZMod 13) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 2 13).mpr (by decide)
  unit_right := by
    change IsUnit (3 : ZMod 13)
    exact (ZMod.isUnit_iff_coprime 3 13).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A13
