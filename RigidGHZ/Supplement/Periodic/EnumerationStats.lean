module

public import RigidGHZ.Supplement.Periodic.BitEnumerationFrom
public import RigidGHZ.Supplement.Periodic.TraceCertificates

/-! Exact configuration sets, transition supports, and their enumerated representations. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

 def configurationSet : Finset (Finset E) := Finset.univ.filter D.LocalConfig
 def transitions : Finset (Finset V × Finset V) :=
  D.configurationSet.image (fun A => (D.input A, D.output A))
 def states : Finset (Finset V) := D.transitions.image Prod.fst ∪ D.transitions.image Prod.snd

@[simp] theorem mem_configurationSet (A : Finset E) : A ∈ D.configurationSet ↔ D.LocalConfig A := by
  simp [configurationSet]

 theorem configurations_card : Fintype.card D.Configurations = D.configurationSet.card := by
  exact Fintype.card_of_subtype D.configurationSet (by intro A; exact D.mem_configurationSet A)

 theorem enumerateFrom_finset (es : List E) (hn : es.Nodup) (hcover : ∀ e, e ∈ es) :
    (D.enumerateFrom es ∅).toFinset = D.configurationSet := by
  ext A
  rw [List.mem_toFinset, D.mem_configurationSet]
  constructor
  · intro hA
    exact D.enumerateFrom_sound es (by constructor <;> simp) hA
  · intro hA
    exact D.enumerateFrom_complete es hn hA (Finset.empty_subset _) (by simp)
      (by intro e he; simpa using hcover e)

 theorem enumerateGroups_sound (gs : List (List E)) {A B : Finset E} (hA : D.Admissible A)
    (hB : B ∈ D.enumerateGroups gs A) : D.LocalConfig B := by
  induction gs generalizing A with
  | nil =>
    simp only [enumerateGroups] at hB
    split_ifs at hB with hinput
    · have heq : B = A := by simpa using hB
      subst B
      exact ⟨hA.1, hA.2, hinput⟩
    · simpa using hB
  | cons g gs ih =>
    obtain ⟨e, he, hB⟩ := List.mem_flatMap.mp hB
    by_cases hc : D.Compatible A e
    · simp only [if_pos hc] at hB
      exact ih (D.admissible_insert hA hc) hB
    · simp only [if_neg hc, List.not_mem_nil] at hB

 theorem enumerateGroups_finset (gs : List (List E))
    (hp : gs.Pairwise (fun g h => Disjoint g.toFinset h.toFinset))
    (hcover : ∀ e, e ∈ gs.flatten)
    (hchoice : ∀ A, D.LocalConfig A → ∀ g ∈ gs, ∃! e, e ∈ g ∧ e ∈ A) :
    (D.enumerateGroups gs ∅).toFinset = D.configurationSet := by
  ext A
  rw [List.mem_toFinset, D.mem_configurationSet]
  constructor
  · intro hA
    exact D.enumerateGroups_sound gs (by constructor <;> simp) hA
  · intro hA
    exact D.enumerateGroups_complete gs hp hA (hchoice A hA) (Finset.empty_subset _) (by simp)
      (by intro e he; simpa using hcover e)

 theorem mem_transitions (s t : Finset V) : (s, t) ∈ D.transitions ↔ D.transferMatrix s t ≠ 0 := by
  simp only [transitions, Finset.mem_image, D.mem_configurationSet, Prod.mk.injEq]
  constructor
  · rintro ⟨A, hA, hs, ht⟩
    change Fintype.card (WeightedWalks.Arc (fun A : D.Configurations => D.input A.1)
      (fun A : D.Configurations => D.output A.1) s t) ≠ 0
    exact Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨⟨⟨A, hA⟩, hs, ht⟩⟩)
  · intro h
    change Fintype.card (WeightedWalks.Arc (fun A : D.Configurations => D.input A.1)
      (fun A : D.Configurations => D.output A.1) s t) ≠ 0 at h
    obtain ⟨⟨⟨A, hA⟩, hs, ht⟩⟩ := Fintype.card_pos_iff.mp (Nat.pos_of_ne_zero h)
    exact ⟨A, hA, hs, ht⟩

 theorem transferMatrix_eq_filter (s t : Finset V) :
    D.transferMatrix s t =
      (D.configurationSet.filter (fun A => D.input A = s ∧ D.output A = t)).card := by
  apply D.transferMatrix_eq_catalog
  · intro A hA
    exact (D.mem_configurationSet A).mp (Finset.mem_filter.mp hA).1
  · intro A hA
    simp only [Finset.mem_filter, D.mem_configurationSet, hA, true_and]


end RigidGHZ.Supplement.Periodic.Scheme
