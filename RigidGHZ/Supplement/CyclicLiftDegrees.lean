module

public import RigidGHZ.Supplement.CyclicLiftData
public import RigidGHZ.Supplement.AffineDegrees

/-! Pair-codegrees of the lifted ordinary hypergraphs. A fixed-bit layer is
linear because two base coordinates determine the affine edge and one sheet
coordinate then determines its unique lift. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators
open UpperBounds

 theorem coordinate_codegree_one {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (p : I → Fin 3 → W → W)
    (hdet : ∀ s t w v (i j : Fin 3), i ≠ j → p s i w = p t i v → p s j w = p t j v →
      (fun k => p s k w) = (fun k => p t k v))
    (X : Finset (Fin 3 × W)) (hX : X.card = 2) :
    codegree (coordinateHypergraph p) X ≤ 1 := by
  classical
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, hijab, rfl⟩ := Finset.card_eq_two.mp hX
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH, hXf⟩ := Finset.mem_filter.mp hf
  obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp heH
  obtain ⟨t, ht, hft⟩ := Finset.mem_biUnion.mp hfH
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hes
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hft
  have hax : a = p s i w := (mem_tupleEdge (x := fun k => p s k w)).mp (hXe (by simp : (i, a) ∈ {(i, a), (j, b)}))
  have hbx : b = p s j w := (mem_tupleEdge (x := fun k => p s k w)).mp (hXe (by simp : (j, b) ∈ {(i, a), (j, b)}))
  have hay : a = p t i v := (mem_tupleEdge (x := fun k => p t k v)).mp (hXf (by simp : (i, a) ∈ {(i, a), (j, b)}))
  have hby : b = p t j v := (mem_tupleEdge (x := fun k => p t k v)).mp (hXf (by simp : (j, b) ∈ {(i, a), (j, b)}))
  have hij : i ≠ j := by
    intro hij
    subst j
    exact hijab (Prod.ext rfl (hax.trans hbx.symm))
  exact congrArg tupleEdge (hdet s t w v i j hij (hax.symm.trans hay) (hbx.symm.trans hby))

 theorem coordinate_bool_product_union {W I : Type*} [Fintype W] [DecidableEq W] [Fintype I]
    (p : Bool × I → Fin 3 → W → W) :
    coordinateHypergraph p = coordinateHypergraph (fun s : I => p (false, s)) ∪
      coordinateHypergraph (fun s : I => p (true, s)) := by
  classical
  ext e
  simp only [coordinateHypergraph, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
  constructor
  · rintro ⟨⟨h, s⟩, he⟩
    cases h
    · exact Or.inl ⟨s, he⟩
    · exact Or.inr ⟨s, he⟩
  · rintro (⟨s, he⟩ | ⟨s, he⟩)
    · exact ⟨(false, s), he⟩
    · exact ⟨(true, s), he⟩

variable {m L : ℕ} [NeZero m] [NeZero L]

 theorem lift_same_bit_pair {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (h : Bool) (s t : S) (w v : ZMod m × ZMod L) (i j : Fin 3)
    (hij : i ≠ j)
    (hi : liftMap lam δ C β (h, s) i w = liftMap lam δ C β (h, t) i v)
    (hj : liftMap lam δ C β (h, s) j w = liftMap lam δ C β (h, t) j v) :
    (fun k => liftMap lam δ C β (h, s) k w) =
      (fun k => liftMap lam δ C β (h, t) k v) := by
  have hb : (fun k => doubleMap lam δ h s.val k w.1) =
      (fun k => doubleMap lam δ h t.val k v.1) := by
    apply triple_eq_of_sum_of_two _ _ i j hij (congrArg Prod.fst hi) (congrArg Prod.fst hj)
    rw [Fin.sum_univ_three, Fin.sum_univ_three]
    exact (double_sum lam δ w.1 s.val h).trans (double_sum lam δ v.1 t.val h).symm
  have ha : w.1 = v.1 := congrFun hb 0
  have hst : s = t := by
    apply Subtype.ext
    have hs := congrFun hb 1
    simpa [doubleMap, ha] using hs
  subst t
  have hx : w.2 = v.2 := by
    have hx := congrArg Prod.snd hi
    simpa only [liftMap, ha, add_left_inj] using hx
  have hw : w = v := Prod.ext ha hx
  rw [hw]

 theorem lift_fixed_codegree {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (h : Bool) (X : Finset (Fin 3 × (ZMod m × ZMod L))) (hX : X.card = 2) :
    codegree (coordinateHypergraph (fun s : S => liftMap lam δ C β (h, s))) X ≤ 1 :=
  coordinate_codegree_one _ (fun s t w v i j hij hi hj =>
    lift_same_bit_pair lam δ C β h s t w v i j hij hi hj) X hX

 theorem lift_codegree {S : Finset (ZMod m)} (lam δ : ZMod m) (C : Marking S)
    (β : ℕ) (X : Finset (Fin 3 × (ZMod m × ZMod L))) (hX : X.card = 2) :
    codegree (coordinateHypergraph (fun hs : Bool × S => liftMap lam δ C β hs)) X ≤ 2 := by
  rw [coordinate_bool_product_union, codegree, Finset.filter_union]
  apply (Finset.card_union_le _ _).trans
  have h0 := lift_fixed_codegree lam δ C β false X hX
  have h1 := lift_fixed_codegree lam δ C β true X hX
  change codegree (coordinateHypergraph (fun s : S => liftMap lam δ C β (false, s))) X +
    codegree (coordinateHypergraph (fun s : S => liftMap lam δ C β (true, s))) X ≤ 2
  omega

end RigidGHZ.Supplement.Affine
