module

public import RigidGHZ.Finite.Seeds.A13Data

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A13
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod 13) := {0,1,2,4,5,8}
def shift (r : Fin 6) : ZMod 13 := (#[0,1,2,4,5,8] : Array (ZMod 13))[r.val]!
def rowIndex (i : Fin 78) : Fin 6 := ⟨i.val / 13, by omega⟩
def column (i : Fin 78) : ZMod 13 := (i.val % 13 : ℕ)
def rootIndex (r : Fin 6) : Fin 78 := ⟨r.val * 13, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem host_eq : data.host = baseGraph (2 : ZMod 13) shifts := by decide +kernel

theorem matching_eq : ∀ r, data.matching r =
    coordinateMatching (baseMap (2 : ZMod 13) (shift r)) := by decide +kernel

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap (2 : ZMod 13) (shift (rowIndex i)) j (column i)) := by
  decide +kernel

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap (2 : ZMod 13) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * 13 →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.A13
