module

public import RigidGHZ.Finite.Seeds.A7Data

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A7
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod 7) := {0,1,2,3}
def shift (r : Fin 4) : ZMod 7 := (#[0,1,2,3] : Array (ZMod 7))[r.val]!
def rowIndex (i : Fin 28) : Fin 4 := ⟨i.val / 7, by omega⟩
def column (i : Fin 28) : ZMod 7 := (i.val % 7 : ℕ)
def rootIndex (r : Fin 4) : Fin 28 := ⟨r.val * 7, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem host_eq : data.host = baseGraph (1 : ZMod 7) shifts := by decide +kernel

theorem matching_eq : ∀ r, data.matching r =
    coordinateMatching (baseMap (1 : ZMod 7) (shift r)) := by decide +kernel

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap (1 : ZMod 7) (shift (rowIndex i)) j (column i)) := by
  decide +kernel

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap (1 : ZMod 7) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * 7 →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.A7
