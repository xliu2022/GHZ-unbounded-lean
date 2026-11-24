module

public import RigidGHZ.Finite.Seeds.A11
public import RigidGHZ.Finite.Seeds.A11Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A11
open RigidGHZ.Supplement.Affine

theorem seed : Seed (2 : ZMod 11) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 2 11).mpr (by decide)
  unit_right := by
    change IsUnit (3 : ZMod 11)
    exact (ZMod.isUnit_iff_coprime 3 11).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A11
