module

public import RigidGHZ.Supplement.Periodic.ElevenEnumerationOutput
public import RigidGHZ.Supplement.Periodic.EnumerationNodup

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Eleven

theorem catalogueList_nodup : catalogueList.Nodup := by
  rw [← enumeration_eq_list]
  rw [bits.enumerateFrom_eq (List.finRange 33) ∅ 0 0 (by decide) (by decide)]
  exact scheme.enumerateFrom_nodup (List.finRange 33) (List.nodup_finRange _) ∅ (by simp)

def catalogue : Finset (Finset (Fin 33)) :=
  ⟨catalogueList, by simpa only [Multiset.coe_nodup] using catalogueList_nodup⟩


theorem catalogue_toFinset : catalogueList.toFinset = catalogue := by
  ext A
  simp [catalogue]



end RigidGHZ.Supplement.Periodic.Eleven
