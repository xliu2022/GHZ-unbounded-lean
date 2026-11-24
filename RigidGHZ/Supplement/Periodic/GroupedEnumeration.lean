module

public import RigidGHZ.Supplement.Periodic.Enumeration

/-! Exact local-configuration search when one edge is required from each
pairwise disjoint group, as in the rows of a Latin square. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

 def enumerateGroups : List (List E) → Finset E → List (Finset E)
  | [], A => if D.input A ⊆ D.allOutgoing then [A] else []
  | g :: gs, A => g.flatMap (fun e =>
      if D.Compatible A e then enumerateGroups gs (insert e A) else [])

 theorem local_group_unique {B : Finset E} (hB : D.LocalConfig B)
    (g : List E) (v : V) (hv : v ∉ D.allOutgoing)
    (hg : ∀ e, e ∈ g ↔ v ∈ D.localPart e) : ∃! e, e ∈ g ∧ e ∈ B := by
  have hloc : v ∈ D.localVertices B := by
    by_contra h
    exact hv (hB.2.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, h⟩))
  obtain ⟨e, heB, hve⟩ := Finset.mem_biUnion.mp hloc
  refine ⟨e, ⟨(hg e).mpr hve, heB⟩, ?_⟩
  rintro f ⟨hfg, hfB⟩
  by_contra hfe
  exact Finset.disjoint_left.mp (hB.1 f hfB e heB hfe) ((hg f).mp hfg) hve

 theorem enumerateGroups_complete (gs : List (List E))
    (hp : gs.Pairwise (fun g h => Disjoint g.toFinset h.toFinset))
    {A B : Finset E} (hB : D.LocalConfig B)
    (hchoice : ∀ g ∈ gs, ∃! e, e ∈ g ∧ e ∈ B)
    (hAB : A ⊆ B) (hdis : Disjoint A gs.flatten.toFinset)
    (hcover : B ⊆ A ∪ gs.flatten.toFinset) : B ∈ D.enumerateGroups gs A := by
  induction gs generalizing A with
  | nil =>
    have hBA : B ⊆ A := by simpa using hcover
    have heq := Finset.Subset.antisymm hAB hBA
    subst A
    simp [enumerateGroups, hB.2.2]
  | cons g gs ih =>
    have hpair := List.pairwise_cons.mp hp
    obtain ⟨e, ⟨heg, heB⟩, heuniq⟩ := hchoice g List.mem_cons_self
    have hne : e ∉ A := by
      intro heA
      apply Finset.disjoint_left.mp hdis heA
      simp only [List.mem_toFinset, List.mem_flatten]
      exact ⟨g, List.mem_cons_self, heg⟩
    have hc := D.compatible_of_local hB hAB heB hne
    have hAB' : insert e A ⊆ B := Finset.insert_subset_iff.mpr ⟨heB, hAB⟩
    have hdis' : Disjoint (insert e A) gs.flatten.toFinset := by
      apply Finset.disjoint_left.mpr
      intro f hf hft
      obtain ⟨g', hg', hfg'⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hft)
      rcases Finset.mem_insert.mp hf with hfe | hfA
      · subst f
        exact Finset.disjoint_left.mp (hpair.1 g' hg')
          (List.mem_toFinset.mpr heg) (List.mem_toFinset.mpr hfg')
      · apply Finset.disjoint_left.mp hdis hfA
        exact List.mem_toFinset.mpr (List.mem_flatten.mpr
          ⟨g', List.mem_cons_of_mem _ hg', hfg'⟩)
    have hcover' : B ⊆ insert e A ∪ gs.flatten.toFinset := by
      intro f hfB
      rcases Finset.mem_union.mp (hcover hfB) with hfA | hfgs
      · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hfA)
      · obtain ⟨g', hg', hfg'⟩ := List.mem_flatten.mp (List.mem_toFinset.mp hfgs)
        rcases List.mem_cons.mp hg' with hgg | hg'
        · subst g'
          have hfe := heuniq f ⟨hfg', hfB⟩
          subst f
          exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
        · exact Finset.mem_union_right _ (List.mem_toFinset.mpr
            (List.mem_flatten.mpr ⟨g', hg', hfg'⟩))
    have hr := ih hpair.2 (fun g' hg' => hchoice g' (List.mem_cons_of_mem _ hg'))
      hAB' hdis' hcover'
    simp only [enumerateGroups, List.mem_flatMap]
    exact ⟨e, heg, by simpa only [if_pos hc] using hr⟩

 theorem property_of_group_enumeration (gs : List (List E))
    (hp : gs.Pairwise (fun g h => Disjoint g.toFinset h.toFinset))
    (hcover : ∀ e, e ∈ gs.flatten)
    (hchoice : ∀ B, D.LocalConfig B → ∀ g ∈ gs, ∃! e, e ∈ g ∧ e ∈ B)
    (P : Finset E → Prop) [DecidablePred P]
    (hcheck : (D.enumerateGroups gs ∅).all (fun A => decide (P A)) = true)
    {A : Finset E} (hA : D.LocalConfig A) : P A := by
  have hm := D.enumerateGroups_complete gs hp hA (hchoice A hA)
    (Finset.empty_subset A) (by simp) (by intro e he; simpa using hcover e)
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) A hm)

 theorem check_group_cons (g : List E) (gs : List (List E)) (A : Finset E)
    (P : Finset E → Prop) [DecidablePred P]
    (h : ∀ e ∈ g, D.Compatible A e →
      (D.enumerateGroups gs (insert e A)).all (fun B => decide (P B)) = true) :
    (D.enumerateGroups (g :: gs) A).all (fun B => decide (P B)) = true := by
  simp only [enumerateGroups, List.all_flatMap]
  apply List.all_eq_true.mpr
  intro e he
  by_cases hc : D.Compatible A e
  · simpa only [if_pos hc] using h e he hc
  · simp only [if_neg hc, List.all_nil]


end RigidGHZ.Supplement.Periodic.Scheme
