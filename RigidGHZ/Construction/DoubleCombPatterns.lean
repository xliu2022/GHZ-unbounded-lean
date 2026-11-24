module

public import RigidGHZ.Selector.DoubleCombArcs
public import RigidGHZ.Construction.OwnerPatterns

@[expose] public section

namespace RigidGHZ.Selector.DoubleComb

open Vertex BlockExpansion RigidGHZ.Rectangle

variable {R : Type*} {T : ℕ} [DecidableEq R] (n : Vertex R T → ℕ)

 theorem upperArcs_pairwise : Pairwise (fun ia jb : R × Fin (T + 1) =>
    Disjoint (upperArcs n ia.1 ia.2) (upperArcs n jb.1 jb.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hf
  have h := congrArg (fun ab : Point n × Point n => ab.2.1) (hk.trans hl.symm)
  exact hne (Prod.ext (Vertex.upper.inj h).1 (Vertex.upper.inj h).2)

 theorem lowerArcs_pairwise : Pairwise (fun ia jb : R × Fin T =>
    Disjoint (lowerArcs n ia.1 ia.2) (lowerArcs n jb.1 jb.2)) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ hne
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hf
  have h := congrArg (fun ab : Point n × Point n => ab.1.1) (hk.trans hl.symm)
  exact hne (Prod.ext (Vertex.lower.inj h).1 (Vertex.lower.inj h).2)

 theorem upperArcs_disjoint_lowerArcs (i j : R) (a : Fin (T + 1)) (b : Fin T) :
    Disjoint (upperArcs n i a) (lowerArcs n j b) := by
  apply Finset.disjoint_left.mpr
  intro e he hf
  obtain ⟨k, _, hk⟩ := Finset.mem_image.mp he
  obtain ⟨l, _, hl⟩ := Finset.mem_image.mp hf
  have h := congrArg (fun ab : Point n × Point n => ab.2.1) (hk.trans hl.symm)
  have hn : ¬ IsUpper (lowerTarget n j b l).1 := by
    unfold lowerTarget lowerNext
    split_ifs <;> simp [first, IsUpper]
  apply hn
  rw [← h]
  trivial

/-- The shared-arc family carrying one paper pattern. -/
def patternArcs (i : R) : Pattern T → Finset (Point n × Point n)
  | .full => upperArcs n i 0
  | .prefix l => lowerArcs n i l
  | .suffix l => upperArcs n i l.succ

/-- The owner chain carrying a pattern. -/
def patternVertex (i : R) : Pattern T → Vertex R T
  | .full => upper i 0
  | .prefix l => lower i l
  | .suffix l => upper i l.succ

@[simp] theorem patternArcs_card (i : R) (p : Pattern T) :
    (patternArcs n i p).card = n (patternVertex i p) + 1 := by
  cases p <;> simp [patternArcs, patternVertex]

 theorem patternArcs_pairwise : Pairwise (fun ip jq : R × Pattern T =>
    Disjoint (patternArcs n ip.1 ip.2) (patternArcs n jq.1 jq.2)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ hne
  cases p with
  | full =>
    cases q with
    | full =>
      apply upperArcs_pairwise n (i := (i, 0)) (j := (j, 0))
      intro h
      exact hne (Prod.ext (Prod.mk.inj h).1 rfl)
    | «prefix» l => exact upperArcs_disjoint_lowerArcs n i j 0 l
    | «suffix» l =>
      apply upperArcs_pairwise n (i := (i, 0)) (j := (j, l.succ))
      intro h
      have hz := congrArg Fin.val (Prod.mk.inj h).2
      simp at hz
  | «prefix» l =>
    cases q with
    | full => exact (upperArcs_disjoint_lowerArcs n j i 0 l).symm
    | «prefix» k =>
      apply lowerArcs_pairwise n (i := (i, l)) (j := (j, k))
      intro h
      exact hne (Prod.ext (Prod.mk.inj h).1 (congrArg Pattern.prefix (Prod.mk.inj h).2))
    | «suffix» k => exact (upperArcs_disjoint_lowerArcs n j i k.succ l).symm
  | «suffix» l =>
    cases q with
    | full =>
      apply upperArcs_pairwise n (i := (i, l.succ)) (j := (j, 0))
      intro h
      have hz := congrArg Fin.val (Prod.mk.inj h).2
      simp at hz
    | «prefix» k => exact upperArcs_disjoint_lowerArcs n i j l.succ k
    | «suffix» k =>
      apply upperArcs_pairwise n (i := (i, l.succ)) (j := (j, k.succ))
      intro h
      exact hne (Prod.ext (Prod.mk.inj h).1
        (congrArg Pattern.suffix (Fin.succ_inj.mp (Prod.mk.inj h).2)))

 theorem patternArcs_nonloop (i : R) (p : Pattern T) {x y : Point n}
    (h : (x, y) ∈ patternArcs n i p) : x ≠ y := by
  cases p with
  | full =>
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    have hh := upperSource_ne n i 0 k
    have hx := congrArg Prod.fst hk
    have hy := congrArg Prod.snd hk
    dsimp at hx hy
    rwa [hx, hy] at hh
  | «prefix» l =>
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    have hh := (lowerTarget_ne n i l k).symm
    have hx := congrArg Prod.fst hk
    have hy := congrArg Prod.snd hk
    dsimp at hx hy
    rwa [hx, hy] at hh
  | «suffix» l =>
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp h
    have hh := upperSource_ne n i l.succ k
    have hx := congrArg Prod.fst hk
    have hy := congrArg Prod.snd hk
    dsimp at hx hy
    rwa [hx, hy] at hh

 theorem patternArcs_occurs_iff (i j : R) (b : Fin (T + 1)) (p : Pattern T)
    {x y : Point n} (h : (x, y) ∈ patternArcs n i p) :
    expandedPerm n j b x = y ↔ i = j ∧ p.occurs b.val := by
  cases p with
  | full => simpa [Pattern.occurs] using upperArcs_occurs_iff n j b i 0 h
  | «prefix» l => exact lowerArcs_occurs_iff n j b i l h
  | «suffix» l =>
    simpa [Pattern.occurs, Nat.succ_le_iff] using upperArcs_occurs_iff n j b i l.succ h

 theorem upperArcs_in_pattern (i : R) (a : Fin (T + 1)) :
    ∃ p : Pattern T, upperArcs n i a = patternArcs n i p := by
  rcases Fin.eq_zero_or_eq_succ a with h | ⟨l, rfl⟩
  · subst a; exact ⟨.full, rfl⟩
  · exact ⟨.suffix l, rfl⟩

 theorem patternArcs_private_unique (hHub : n hub = 0)
    (ib jc : R × Fin (T + 1)) (x : Point n)
    (hm : expandedPerm n ib.1 ib.2 x ≠ x)
    (hp : ∀ ip : R × Pattern T, (x, expandedPerm n ib.1 ib.2 x) ∉ patternArcs n ip.1 ip.2)
    (heq : expandedPerm n ib.1 ib.2 x = expandedPerm n jc.1 jc.2 x) : ib = jc := by
  apply expanded_private_unique n ib jc x _ heq
  intro hS
  rcases shared_arc_cases n hHub ib.1 ib.2 x hS with h | ⟨j, a, h⟩ | ⟨j, a, h⟩
  · exact hm h
  · obtain ⟨p, he⟩ := upperArcs_in_pattern n j a
    rw [he] at h
    exact hp (j, p) h
  · exact hp (j, Pattern.prefix a) h

end RigidGHZ.Selector.DoubleComb
