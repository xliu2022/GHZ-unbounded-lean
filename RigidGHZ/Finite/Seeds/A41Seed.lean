module

public import RigidGHZ.Finite.Seeds.A41
public import RigidGHZ.Finite.Seeds.A41Facts

@[expose] public section
namespace RigidGHZ.Finite.Seeds.A41
open RigidGHZ.Supplement.Affine

theorem seed : Seed (1 : ZMod 41) shifts where
  unit_left := (ZMod.isUnit_iff_coprime 1 41).mpr (by decide)
  unit_right := by
    change IsUnit (2 : ZMod 41)
    exact (ZMod.isUnit_iff_coprime 2 41).mpr (by decide)
  complete := by
    intro M hM
    obtain ⟨r,hr⟩ := complete M (by simpa only [host_eq] using hM)
    exact ⟨⟨shift r,shift_mem r⟩,hr.trans (matching_eq r)⟩

end RigidGHZ.Finite.Seeds.A41
