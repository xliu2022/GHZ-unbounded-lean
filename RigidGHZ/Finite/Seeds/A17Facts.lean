module

public import RigidGHZ.Finite.Seeds.A17Data

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A17
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod 17) := {0,1,2,4,5}
def shift (r : Fin 5) : ZMod 17 := (#[0,1,2,4,5] : Array (ZMod 17))[r.val]!
def rowIndex (i : Fin 85) : Fin 5 := ⟨i.val / 17, by omega⟩
def column (i : Fin 85) : ZMod 17 := (i.val % 17 : ℕ)
def rootIndex (r : Fin 5) : Fin 85 := ⟨r.val * 17, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem host_eq : data.host = baseGraph (2 : ZMod 17) shifts := by decide +kernel

theorem matching_eq : ∀ r, data.matching r =
    coordinateMatching (baseMap (2 : ZMod 17) (shift r)) := by decide +kernel

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap (2 : ZMod 17) (shift (rowIndex i)) j (column i)) := by
  decide +kernel

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap (2 : ZMod 17) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * 17 →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.A17
