module

public import RigidGHZ.Supplement.CyclicLift
public import RigidGHZ.Supplement.LinearLiftPairs

/-! Linear refinements of marked cyclic lifts: all sheets for L >= 4,
monotone three-sheet codes, and the exact prescribed deletions for two sheets. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open UpperBounds

 theorem coordinateHypergraph_finset {W I : Type*} [Fintype W] [DecidableEq W]
    [Fintype I] [DecidableEq I] (p : I → Fin 3 → W → W) (R : Finset I) :
    coordinateHypergraph (fun i : R => p i.val) = R.biUnion (fun i => coordinateMatching (p i)) := by
  ext e
  simp [coordinateHypergraph]

variable {m L : ℕ} [NeZero m] [NeZero L]

/-- Deleting whole prescribed matching classes retains complete classification
of every ordinary perfect matching of the remaining lift. -/
def Seed.retainedFamily {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S) (β : ℕ) (R : Finset (Bool × S)) :
    RigidFamily (coordinateHypergraph (fun hs : R => liftMap (L := L) lam δ C β hs.val)) R := by
  let F := B.cyclicFamily hm hodd hcop δ hδ C β
  have heq : coordinateHypergraph (fun hs : R => liftMap (L := L) lam δ C β hs.val) =
      R.biUnion F.matching := coordinateHypergraph_finset _ R
  rw [heq]
  exact F.restrict R

/-- General retained-class linearity theorem, with the only possible
cross-bit collision displayed as an explicit modular inequality. -/
 theorem Seed.linear_retained {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S) (hL : 2 ≤ L) (R : Finset (Bool × S))
    (hsep : ∀ s t : S, (false, s) ∈ R → (true, t) ∈ R → ∀ a,
      t.val = s.val + δ →
        (bit (C.code t a) : ZMod L) + 2 ≠ (bit (C.code s a) : ZMod L)) :
    ∃ H : Hypergraph (Fin 3 × (ZMod m × ZMod L)),
      H = coordinateHypergraph (fun hs : R => liftMap (L := L) lam δ C 1 hs.val) ∧
      Uniform H 3 ∧ BalancedPartite H 3 (m * L) ∧ IsRigid H R.card ∧ maxDegree H 2 ≤ 1 := by
  let H := coordinateHypergraph (fun hs : R => liftMap (L := L) lam δ C 1 hs.val)
  refine ⟨H, rfl, ?_, ?_, ?_, ?_⟩
  · simpa using coordinateHypergraph_uniform (fun hs : R => liftMap (L := L) lam δ C 1 hs.val)
  · simpa using coordinateHypergraph_balanced (fun hs : R => liftMap (L := L) lam δ C 1 hs.val)
  · let e : Fin R.card ≃ R := (Fintype.equivFinOfCardEq (by simp)).symm
    exact ⟨(B.retainedFamily hm hodd hcop δ hδ C 1 R).reindex e⟩
  · exact maxDegree_le H 2 1 (retained_codegree_one lam δ C hL R hsep)

/-- For every period at least four, all doubled matching classes are retained
and the actual lifted hypergraph is linear. -/
 theorem Seed.linear_large {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S) (hL : 4 ≤ L) :
    ∃ H : Hypergraph (Fin 3 × (ZMod m × ZMod L)),
      H = coordinateHypergraph (fun hs : Bool × S => liftMap (L := L) lam δ C 1 hs) ∧
      Uniform H 3 ∧ BalancedPartite H 3 (m * L) ∧ IsRigid H (2 * S.card) ∧ maxDegree H 2 ≤ 1 := by
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_retained hm hodd hcop δ hδ C
    (by omega) Finset.univ (by
      intro s t hs ht a he
      exact bits_separated_large hL (C.code s a) (C.code t a))
  refine ⟨H, ?_, hU, hP, ?_, hD⟩
  · rw [hH, coordinateHypergraph_finset]
    rfl
  · simpa using hR

/-- Three sheets: monotonicity along the shift arcs removes the sole remaining
collision, whose sheet displacement would otherwise be three. -/
 theorem Seed.linear_three {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (hcop : m.Coprime 3) (δ : ZMod m) (hδ : IsUnit δ)
    (C : Marking S)
    (hmono : ∀ s t : S, t.val = s.val + δ → ∀ a, bit (C.code t a) ≤ bit (C.code s a)) :
    ∃ H : Hypergraph (Fin 3 × (ZMod m × ZMod 3)),
      H = coordinateHypergraph (fun hs : Bool × S => liftMap (L := 3) lam δ C 1 hs) ∧
      Uniform H 3 ∧ BalancedPartite H 3 (m * 3) ∧ IsRigid H (2 * S.card) ∧ maxDegree H 2 ≤ 1 := by
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_retained hm hodd hcop δ hδ C
    (by decide : 2 ≤ 3) Finset.univ (by
      intro s t hs ht a he
      exact bits_separated_three (C.code s a) (C.code t a) (hmono s t he a))
  refine ⟨H, ?_, hU, hP, ?_, hD⟩
  · rw [hH, coordinateHypergraph_finset]
    rfl
  · simpa using hR

/-- The shifts whose bit-one matching is deleted in the two-sheet refinement. -/
def shiftOverlap (S : Finset (ZMod m)) (δ : ZMod m) : Finset (ZMod m) :=
  S ∩ S.image (fun s => s + δ)

 def deletedClasses (S : Finset (ZMod m)) (δ : ZMod m) : Finset (Bool × S) :=
  (shiftOverlap S δ).attach.image (fun t =>
    (true, (⟨t.val, (Finset.mem_inter.mp t.property).1⟩ : S)))

 def retainedTwo (S : Finset (ZMod m)) (δ : ZMod m) : Finset (Bool × S) :=
  Finset.univ \ deletedClasses S δ

 theorem deletedClasses_card (S : Finset (ZMod m)) (δ : ZMod m) :
    (deletedClasses S δ).card = (shiftOverlap S δ).card := by
  rw [deletedClasses, Finset.card_image_of_injective]
  · simp
  · intro s t h
    apply Subtype.ext
    exact congrArg (fun p : Bool × S => p.2.val) h

 theorem retainedTwo_card (S : Finset (ZMod m)) (δ : ZMod m) :
    (retainedTwo S δ).card = 2 * S.card - (shiftOverlap S δ).card := by
  rw [retainedTwo, Finset.card_sdiff_of_subset (Finset.subset_univ _), deletedClasses_card]
  simp

 theorem shifted_class_deleted {S : Finset (ZMod m)} (δ : ZMod m) (s t : S)
    (ht : t.val = s.val + δ) : (true, t) ∈ deletedClasses S δ := by
  have htmem : t.val ∈ shiftOverlap S δ := by
    apply Finset.mem_inter.mpr
    refine ⟨t.property, Finset.mem_image.mpr ⟨s.val, s.property, ht.symm⟩⟩
  exact Finset.mem_image.mpr ⟨⟨t.val, htmem⟩, Finset.mem_attach _ _, rfl⟩

/-- Two sheets: deleting precisely the bit-one classes with shifts in
`S ∩ (S + δ)` gives the printed count and a linear rigid ordinary hypergraph. -/
 theorem Seed.linear_two {S : Finset (ZMod m)} {lam : ZMod m} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (δ : ZMod m) (hδ : IsUnit δ) (C : Marking S) :
    ∃ H : Hypergraph (Fin 3 × (ZMod m × ZMod 2)),
      H = coordinateHypergraph (fun hs : retainedTwo S δ => liftMap (L := 2) lam δ C 1 hs.val) ∧
      Uniform H 3 ∧ BalancedPartite H 3 (m * 2) ∧
      IsRigid H (2 * S.card - (shiftOverlap S δ).card) ∧ maxDegree H 2 ≤ 1 := by
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_retained hm hodd hodd.coprime_two_right δ hδ C
    (by decide : 2 ≤ 2) (retainedTwo S δ) (by
      intro s t hs ht a he
      exact ((Finset.mem_sdiff.mp ht).2 (shifted_class_deleted δ s t he)).elim)
  refine ⟨H, hH, hU, hP, ?_, hD⟩
  simpa only [retainedTwo_card] using hR

end RigidGHZ.Supplement.Affine
