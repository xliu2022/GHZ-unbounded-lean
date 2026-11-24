module

public import RigidGHZ.Supplement.Periodic.GroupedEnumeration

/-! The proved-complete searches enumerate each configuration exactly once. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

 theorem enumerateFrom_bounds {es : List E} {A B : Finset E}
    (hB : B ∈ D.enumerateFrom es A) : A ⊆ B ∧ B ⊆ A ∪ es.toFinset := by
  induction es generalizing A with
  | nil =>
    by_cases h : D.input A ⊆ D.allOutgoing
    · have he : B = A := by simpa only [enumerateFrom, ite_eq_left h, List.mem_singleton] using hB
      subst B
      simp
    · simp only [enumerateFrom, ite_eq_right h, List.not_mem_nil] at hB
  | cons e es ih =>
    simp only [enumerateFrom, List.mem_append] at hB
    rcases hB with hB | hB
    · obtain ⟨hAB, hBA⟩ := ih hB
      refine ⟨hAB, hBA.trans ?_⟩
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (by
          rw [List.toFinset_cons]
          exact Finset.mem_insert_of_mem hx)
    · by_cases h : D.Compatible A e
      · simp only [ite_eq_left h] at hB
        obtain ⟨hAB, hBA⟩ := ih hB
        refine ⟨(Finset.subset_insert _ _).trans hAB, ?_⟩
        intro x hx
        have hb := hBA hx
        simpa only [Finset.mem_union, Finset.mem_insert, List.toFinset_cons, or_assoc,
          or_left_comm] using hb
      · simp only [ite_eq_right h, List.not_mem_nil] at hB

 theorem enumerateFrom_nodup (es : List E) (hn : es.Nodup) (A : Finset E)
    (hdis : Disjoint A es.toFinset) : (D.enumerateFrom es A).Nodup := by
  induction es generalizing A with
  | nil =>
    simp only [enumerateFrom]
    split_ifs <;> simp
  | cons e es ih =>
    have hn' := List.nodup_cons.mp hn
    have hds : Disjoint A es.toFinset := hdis.mono_right (by
      intro x hx
      simp only [List.toFinset_cons]
      exact Finset.mem_insert_of_mem hx)
    have hdins : Disjoint (insert e A) es.toFinset := by
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hn'.1 (List.mem_toFinset.mp hx')
      · exact Finset.disjoint_left.mp hds hx hx'
    by_cases hc : D.Compatible A e
    · rw [enumerateFrom, ite_eq_left hc]
      apply (ih (A := A) hn'.2 hds).append (ih (A := insert e A) hn'.2 hdins)
      apply List.disjoint_left.mpr
      intro B hleft hright
      have hb := (D.enumerateFrom_bounds hright).1 (Finset.mem_insert_self e A)
      rcases Finset.mem_union.mp ((D.enumerateFrom_bounds hleft).2 hb) with heA | hees
      · exact Finset.disjoint_left.mp hdis heA (by simp)
      · exact hn'.1 (List.mem_toFinset.mp hees)
    · rw [enumerateFrom, ite_eq_right hc, List.append_nil]
      exact ih (A := A) hn'.2 hds

 theorem enumerateGroups_bounds {gs : List (List E)} {A B : Finset E}
    (hB : B ∈ D.enumerateGroups gs A) : A ⊆ B ∧ B ⊆ A ∪ gs.flatten.toFinset := by
  induction gs generalizing A with
  | nil =>
    by_cases h : D.input A ⊆ D.allOutgoing
    · have he : B = A := by simpa only [enumerateGroups, ite_eq_left h, List.mem_singleton] using hB
      subst B
      simp
    · simp only [enumerateGroups, ite_eq_right h, List.not_mem_nil] at hB
  | cons g gs ih =>
    obtain ⟨e, he, hB⟩ := List.mem_flatMap.mp hB
    by_cases hc : D.Compatible A e
    · simp only [ite_eq_left hc] at hB
      obtain ⟨hAB, hBA⟩ := ih hB
      refine ⟨(Finset.subset_insert _ _).trans hAB, ?_⟩
      intro x hx
      rcases Finset.mem_union.mp (hBA hx) with hx | hx
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
            (by simpa only [List.flatten_cons, List.mem_append] using Or.inl he))
        · exact Finset.mem_union_left _ hx
      · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
          (by simpa only [List.flatten_cons, List.mem_append] using Or.inr (List.mem_toFinset.mp hx)))
    · simp only [ite_eq_right hc, List.not_mem_nil] at hB

 theorem enumerateGroups_nodup (gs : List (List E)) (hn : gs.flatten.Nodup) (A : Finset E)
    (hdis : Disjoint A gs.flatten.toFinset) : (D.enumerateGroups gs A).Nodup := by
  induction gs generalizing A with
  | nil =>
    simp only [enumerateGroups]
    split_ifs <;> simp
  | cons g gs ih =>
    change (g ++ gs.flatten).Nodup at hn
    have hn' := List.nodup_append'.mp hn
    have hds : Disjoint A gs.flatten.toFinset := hdis.mono_right (by
      intro x hx
      exact List.mem_toFinset.mpr (List.mem_append.mpr (Or.inr (List.mem_toFinset.mp hx))))
    have hdins : ∀ e ∈ g, Disjoint (insert e A) gs.flatten.toFinset := by
      intro e he
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact List.disjoint_left.mp hn'.2.2 he (List.mem_toFinset.mp hx')
      · exact Finset.disjoint_left.mp hds hx hx'
    rw [enumerateGroups]
    apply List.nodup_flatMap.mpr
    constructor
    · intro e he
      by_cases hc : D.Compatible A e
      · simp only [ite_eq_left hc]
        exact ih (A := insert e A) hn'.2.1 (hdins e he)
      · simp only [ite_eq_right hc, List.nodup_nil]
    · refine List.Pairwise.imp_of_mem ?_ hn'.1
      intro e f he hf hef
      dsimp only [Function.onFun]
      by_cases hec : D.Compatible A e
      · by_cases hfc : D.Compatible A f
        · simp only [ite_eq_left hec, ite_eq_left hfc]
          apply List.disjoint_left.mpr
          intro B hBe hBf
          have hb := (D.enumerateGroups_bounds hBe).1 (Finset.mem_insert_self e A)
          rcases Finset.mem_union.mp ((D.enumerateGroups_bounds hBf).2 hb) with heA | hegs
          · rcases Finset.mem_insert.mp heA with hef' | heA
            · exact hef hef'
            · exact Finset.disjoint_left.mp hdis heA (List.mem_toFinset.mpr
                (by simpa only [List.flatten_cons, List.mem_append] using Or.inl he))
          · exact List.disjoint_left.mp hn'.2.2 he (List.mem_toFinset.mp hegs)
        · simp only [ite_eq_right hfc, List.disjoint_nil_right]
      · simp only [ite_eq_right hec, List.disjoint_nil_left]

end RigidGHZ.Supplement.Periodic.Scheme
