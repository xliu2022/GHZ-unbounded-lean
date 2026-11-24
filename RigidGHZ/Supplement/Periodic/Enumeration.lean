module

public import RigidGHZ.Supplement.Periodic.Basic

/-! An exact pruning enumerator for local configurations. Its completeness is
proved once; finite height certificates can then be checked on the short list. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

instance (A : Finset E) : Decidable (D.LocalConfig A) := inferInstanceAs (Decidable
  ((∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.localPart e) (D.localPart f)) ∧
  (∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.outgoing e) (D.outgoing f)) ∧
  D.input A ⊆ D.allOutgoing))

 def Admissible (A : Finset E) : Prop :=
  (∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.localPart e) (D.localPart f)) ∧
  (∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.outgoing e) (D.outgoing f))

 def Compatible (A : Finset E) (e : E) : Prop :=
  Disjoint (D.localVertices A) (D.localPart e) ∧ Disjoint (D.output A) (D.outgoing e)

instance (A : Finset E) (e : E) : Decidable (D.Compatible A e) := inferInstanceAs
  (Decidable (Disjoint (D.localVertices A) (D.localPart e) ∧ Disjoint (D.output A) (D.outgoing e)))

 def enumerateFrom : List E → Finset E → List (Finset E)
  | [], A => if D.input A ⊆ D.allOutgoing then [A] else []
  | e :: es, A => enumerateFrom es A ++
      if D.Compatible A e then enumerateFrom es (insert e A) else []

 theorem compatible_of_local {A B : Finset E} {e : E} (hB : D.LocalConfig B)
    (hAB : A ⊆ B) (he : e ∈ B) (hne : e ∉ A) : D.Compatible A e := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro v hvA hve
    obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
    have hfe : f ≠ e := by intro h; exact hne (h ▸ hf)
    exact Finset.disjoint_left.mp (hB.1 f (hAB hf) e he hfe) hvf hve
  · apply Finset.disjoint_left.mpr
    intro v hvA hve
    obtain ⟨f, hf, hvf⟩ := Finset.mem_biUnion.mp hvA
    have hfe : f ≠ e := by intro h; exact hne (h ▸ hf)
    exact Finset.disjoint_left.mp (hB.2.1 f (hAB hf) e he hfe) hvf hve

/-- Every local configuration occurs in the exact search. -/
theorem enumerateFrom_complete (es : List E) (hn : es.Nodup) {A B : Finset E}
    (hB : D.LocalConfig B) (hAB : A ⊆ B) (hdis : Disjoint A es.toFinset)
    (hcover : B ⊆ A ∪ es.toFinset) : B ∈ D.enumerateFrom es A := by
  induction es generalizing A with
  | nil =>
    have hBA : B ⊆ A := by simpa using hcover
    have heq : A = B := Finset.Subset.antisymm hAB hBA
    subst A
    simp [enumerateFrom, hB.2.2]
  | cons e es ih =>
    have hnodup := List.nodup_cons.mp hn
    by_cases he : e ∈ B
    · have hne : e ∉ A := by
        intro heA
        exact Finset.disjoint_left.mp hdis heA (by simp)
      have hcomp := D.compatible_of_local hB hAB he hne
      have hAB' : insert e A ⊆ B := Finset.insert_subset_iff.mpr ⟨he, hAB⟩
      have hdis' : Disjoint (insert e A) es.toFinset := by
        apply Finset.disjoint_left.mpr
        intro f hf hfes
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact hnodup.1 (by simpa using hfes)
        · exact Finset.disjoint_left.mp hdis hf (by simp only [List.toFinset_cons]; exact Finset.mem_insert_of_mem hfes)
      have hcover' : B ⊆ insert e A ∪ es.toFinset := by
        intro f hf
        rcases Finset.mem_union.mp (hcover hf) with hfA | hfes
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem hfA)
        · simp only [List.toFinset_cons, Finset.mem_insert] at hfes
          rcases hfes with rfl | hfes
          · exact Finset.mem_union_left _ (Finset.mem_insert_self _ _)
          · exact Finset.mem_union_right _ hfes
      have hr := ih hnodup.2 hAB' hdis' hcover'
      simp only [enumerateFrom, if_pos hcomp, List.mem_append]
      exact Or.inr hr
    · have hdis' : Disjoint A es.toFinset := hdis.mono_right (by
        intro f hf; simp only [List.toFinset_cons]; exact Finset.mem_insert_of_mem hf)
      have hcover' : B ⊆ A ∪ es.toFinset := by
        intro f hf
        rcases Finset.mem_union.mp (hcover hf) with hfA | hfes
        · exact Finset.mem_union_left _ hfA
        · simp only [List.toFinset_cons, Finset.mem_insert] at hfes
          rcases hfes with rfl | hfes
          · exact (he hf).elim
          · exact Finset.mem_union_right _ hfes
      have hr := ih hnodup.2 hAB hdis' hcover'
      simp only [enumerateFrom, List.mem_append]
      exact Or.inl hr

 theorem admissible_insert {A : Finset E} {e : E} (hA : D.Admissible A)
    (hcomp : D.Compatible A e) : D.Admissible (insert e A) := by
  have hl : ∀ f ∈ A, D.localPart f ⊆ D.localVertices A := by
    intro f hf v hv
    exact Finset.mem_biUnion.mpr ⟨f, hf, hv⟩
  have ho : ∀ f ∈ A, D.outgoing f ⊆ D.output A := by
    intro f hf v hv
    exact Finset.mem_biUnion.mpr ⟨f, hf, hv⟩
  constructor
  · intro f hf g hg hfg
    rcases Finset.mem_insert.mp hf with hfe | hfA
    · subst f
      rcases Finset.mem_insert.mp hg with hge | hgA
      · exact (hfg hge.symm).elim
      · exact (hcomp.1.mono_left (hl g hgA)).symm
    · rcases Finset.mem_insert.mp hg with hge | hgA
      · subst g
        exact hcomp.1.mono_left (hl f hfA)
      · exact hA.1 f hfA g hgA hfg
  · intro f hf g hg hfg
    rcases Finset.mem_insert.mp hf with hfe | hfA
    · subst f
      rcases Finset.mem_insert.mp hg with hge | hgA
      · exact (hfg hge.symm).elim
      · exact (hcomp.2.mono_left (ho g hgA)).symm
    · rcases Finset.mem_insert.mp hg with hge | hgA
      · subst g
        exact hcomp.2.mono_left (ho f hfA)
      · exact hA.2 f hfA g hgA hfg

 theorem enumerateFrom_sound (es : List E) {A B : Finset E} (hA : D.Admissible A)
    (hB : B ∈ D.enumerateFrom es A) : D.LocalConfig B := by
  induction es generalizing A with
  | nil =>
    simp only [enumerateFrom] at hB
    split_ifs at hB with hinput
    · have heq : B = A := by simpa using hB
      subst B
      exact ⟨hA.1, hA.2, hinput⟩
    · simpa using hB
  | cons e es ih =>
    simp only [enumerateFrom, List.mem_append] at hB
    rcases hB with hB | hB
    · exact ih hA hB
    · split_ifs at hB with hc
      · exact ih (D.admissible_insert hA hc) hB
      · simpa using hB

/-- A Boolean check over the generated list yields a theorem for every actual
local configuration. No external enumeration result is trusted. -/
theorem property_of_enumeration (es : List E) (hn : es.Nodup) (hcover : ∀ e, e ∈ es)
    (P : Finset E → Prop) [DecidablePred P]
    (hcheck : (D.enumerateFrom es ∅).all (fun A => decide (P A)) = true)
    {A : Finset E} (hA : D.LocalConfig A) : P A := by
  have hm : A ∈ D.enumerateFrom es ∅ := D.enumerateFrom_complete es hn hA
    (Finset.empty_subset _) (by simp) (by intro e he; simpa using hcover e)
  exact of_decide_eq_true ((List.all_eq_true.mp hcheck) A hm)


/-- Compositional certificate rules: each pruning decision and terminal
configuration is checked independently by the kernel. -/
theorem check_enumeration_skip (e : E) (es : List E) (A : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (hc : ¬D.Compatible A e)
    (h : (D.enumerateFrom es A).all (fun B => decide (P B)) = true) :
    (D.enumerateFrom (e :: es) A).all (fun B => decide (P B)) = true := by
  simpa only [enumerateFrom, if_neg hc, List.append_nil] using h

 theorem check_enumeration_split (e : E) (es : List E) (A : Finset E)
    (P : Finset E → Prop) [DecidablePred P] (hc : D.Compatible A e)
    (h₀ : (D.enumerateFrom es A).all (fun B => decide (P B)) = true)
    (h₁ : (D.enumerateFrom es (insert e A)).all (fun B => decide (P B)) = true) :
    (D.enumerateFrom (e :: es) A).all (fun B => decide (P B)) = true := by
  simp only [enumerateFrom, if_pos hc, List.all_append, h₀, h₁, Bool.and_self]

end RigidGHZ.Supplement.Periodic.Scheme
