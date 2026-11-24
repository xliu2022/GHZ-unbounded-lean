module

public import RigidGHZ.Supplement.Periodic.TenEnumerationOutput
public import RigidGHZ.Supplement.Periodic.EnumerationNodup

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Ten

theorem catalogueList_nodup : catalogueList.Nodup := by
  rw [← enumeration_eq_list]
  rw [bits.enumerateFrom_eq (List.finRange 20) ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateFrom_nodup (List.finRange 20) (List.nodup_finRange _) ∅ (by simp)

def catalogue : Finset (Finset (Fin 20)) :=
  ⟨catalogueList, by simpa only [Multiset.coe_nodup] using catalogueList_nodup⟩

theorem catalogue_toFinset : catalogueList.toFinset = catalogue := by
  ext A
  simp [catalogue]


end RigidGHZ.Supplement.Periodic.Ten
