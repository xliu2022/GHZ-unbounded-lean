module

public import RigidGHZ.Supplement.Periodic.LatinEnumerationOutput
public import RigidGHZ.Supplement.Periodic.EnumerationNodup

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Latin

theorem catalogueList_nodup : catalogueList.Nodup := by
  rw [← enumeration_eq_list]
  rw [bits.enumerate_eq groups ∅ 0 0 (by decide) (by decide)]
  apply scheme.enumerateGroups_nodup groups
  · have he : groups.flatten = List.finRange 64 := by decide
    rw [he]
    exact List.nodup_finRange _
  · simp

def catalogue : Finset (Finset (Fin 64)) :=
  ⟨catalogueList, by simpa only [Multiset.coe_nodup] using catalogueList_nodup⟩

theorem catalogue_toFinset : catalogueList.toFinset = catalogue := by
  ext A
  simp [catalogue]


end RigidGHZ.Supplement.Periodic.Latin
