module

public import RigidGHZ.Finite.Seeds.A29
public import RigidGHZ.Finite.Seeds.A29Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A29
open RigidGHZ.Supplement.Affine

theorem seed : Seed (8 : ZMod 29) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 8 29).mpr (by decide)
  unit_right := by
    change IsUnit (9 : ZMod 29)
    exact (ZMod.isUnit_iff_coprime 9 29).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A29
