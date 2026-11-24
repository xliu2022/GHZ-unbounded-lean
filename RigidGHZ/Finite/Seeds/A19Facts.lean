module

public import RigidGHZ.Finite.Seeds.A19Data
public import RigidGHZ.Finite.ExactCoverIndex

/-! Kernel-checked identification of the explicit table with the paper's affine
formulas, including the ordering facts used in translation normalization. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A19
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def shifts : Finset (ZMod 19) := {0,1,3,12,14,15}
def shift (r : Fin 6) : ZMod 19 := (#[0,1,3,12,14,15] : Array (ZMod 19))[r.val]!
def rowIndex (i : Fin 114) : Fin 6 := ⟨i.val / 19, by omega⟩
def column (i : Fin 114) : ZMod 19 := (i.val % 19 : ℕ)
def rootIndex (r : Fin 6) : Fin 114 := ⟨r.val * 19, by omega⟩

theorem shift_mem : ∀ r, shift r ∈ shifts := by decide +kernel

theorem shift_surjective : ∀ s : shifts, ∃ r, shift r = s.val := by decide +kernel

theorem matching_eq_0 : data.matching 0 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 0)) := by decide +kernel

theorem matching_eq_1 : data.matching 1 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 1)) := by decide +kernel

theorem matching_eq_2 : data.matching 2 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 2)) := by decide +kernel

theorem matching_eq_3 : data.matching 3 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 3)) := by decide +kernel

theorem matching_eq_4 : data.matching 4 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 4)) := by decide +kernel

theorem matching_eq_5 : data.matching 5 =
    coordinateMatching (baseMap (3 : ZMod 19) (shift 5)) := by decide +kernel

theorem matching_eq (r : Fin 6) : data.matching r =
    coordinateMatching (baseMap (3 : ZMod 19) (shift r)) := by
  fin_cases r
  · exact matching_eq_0
  · exact matching_eq_1
  · exact matching_eq_2
  · exact matching_eq_3
  · exact matching_eq_4
  · exact matching_eq_5

theorem host_eq : data.host = baseGraph (3 : ZMod 19) shifts :=
  affine_host_eq_of_rows data (3 : ZMod 19) shifts shift shift_mem shift_surjective
    matching_eq valid.covers

theorem edge_eq : ∀ i, data.edge i =
    tupleEdge (fun j => baseMap (3 : ZMod 19) (shift (rowIndex i)) j (column i)) := by
  decide +kernel

theorem root_edge_eq : ∀ r, data.edge (rootIndex r) =
    tupleEdge (fun j => baseMap (3 : ZMod 19) (shift r) j 0) := by decide +kernel

theorem lower_shift : ∀ r i, i.val < r.val * 19 →
    (shift (rowIndex i)).val < (shift r).val := by decide +kernel

end RigidGHZ.Finite.Seeds.A19
