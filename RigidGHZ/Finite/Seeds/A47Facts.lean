module

public import RigidGHZ.Finite.Seeds.A47Data
public import RigidGHZ.Finite.ExactCoverIndex

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod 47) := {0,1,2,11,23}
def shift (r : Fin 5) : ZMod 47 := (#[0,1,2,11,23] : Array (ZMod 47))[r.val]!
def rowIndex (i : Fin 235) : Fin 5 := ⟨i.val / 47, by omega⟩
def column (i : Fin 235) : ZMod 47 := (i.val % 47 : ℕ)
def rootIndex (r : Fin 5) : Fin 235 := ⟨r.val * 47, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem matching_eq_0 : data.matching 0 =
    coordinateMatching (baseMap (1 : ZMod 47) (shift 0)) := by decide +kernel

theorem matching_eq_1 : data.matching 1 =
    coordinateMatching (baseMap (1 : ZMod 47) (shift 1)) := by decide +kernel

theorem matching_eq_2 : data.matching 2 =
    coordinateMatching (baseMap (1 : ZMod 47) (shift 2)) := by decide +kernel

theorem matching_eq_3 : data.matching 3 =
    coordinateMatching (baseMap (1 : ZMod 47) (shift 3)) := by decide +kernel

theorem matching_eq_4 : data.matching 4 =
    coordinateMatching (baseMap (1 : ZMod 47) (shift 4)) := by decide +kernel

theorem matching_eq (r : Fin 5) : data.matching r =
    coordinateMatching (baseMap (1 : ZMod 47) (shift r)) := by
  fin_cases r
  · exact matching_eq_0
  · exact matching_eq_1
  · exact matching_eq_2
  · exact matching_eq_3
  · exact matching_eq_4

theorem host_eq : data.host = baseGraph (1 : ZMod 47) shifts :=
  affine_host_eq_of_rows data (1 : ZMod 47) shifts shift shift_mem shift_surjective
    matching_eq table_covers

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap (1 : ZMod 47) (shift (rowIndex i)) j (column i)) := by
  exact affine_edge_formula

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap (1 : ZMod 47) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * 47 →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.A47
