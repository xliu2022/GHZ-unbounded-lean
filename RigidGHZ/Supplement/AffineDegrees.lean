module

public import RigidGHZ.Supplement.AffineDoubling
public import RigidGHZ.Supplement.GraftDegrees

/-! Pair-codegree bounds for the genuine ordinary affine hypergraphs. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators
open UpperBounds

 theorem triple_eq_of_sum_of_two {A : Type*} [AddCommGroup A]
    (x y : Fin 3 → A) (i j : Fin 3) (hij : i ≠ j)
    (hi : x i = y i) (hj : x j = y j) (hsum : ∑ k, x k = ∑ k, y k) : x = y := by
  fin_cases i <;> fin_cases j <;>
    simp_all [Fin.sum_univ_three]
  all_goals
    funext k
    fin_cases k <;> simp_all

/-- Any triple family with one constant coordinate sum is linear, in the
standard codegree sense on arbitrary pairs of its ordinary vertices. -/
 theorem constant_sum_codegree {A : Type*} [AddCommGroup A] [DecidableEq A]
    (H : Hypergraph (Fin 3 × A)) (t : A)
    (hH : ∀ e ∈ H, ∃ x : Fin 3 → A, e = tupleEdge x ∧ ∑ k, x k = t)
    (X : Finset (Fin 3 × A)) (hX : X.card = 2) : codegree H X ≤ 1 := by
  classical
  obtain ⟨⟨i, a⟩, ⟨j, b⟩, hijab, rfl⟩ := Finset.card_eq_two.mp hX
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he
  obtain ⟨hfH, hXf⟩ := Finset.mem_filter.mp hf
  obtain ⟨x, rfl, hx⟩ := hH e heH
  obtain ⟨y, rfl, hy⟩ := hH f hfH
  have hax : a = x i := mem_tupleEdge.mp (hXe (by simp))
  have hbx : b = x j := mem_tupleEdge.mp (hXe (by simp))
  have hay : a = y i := mem_tupleEdge.mp (hXf (by simp))
  have hby : b = y j := mem_tupleEdge.mp (hXf (by simp))
  have hij : i ≠ j := by
    intro h
    subst j
    exact hijab (Prod.ext rfl (hax.trans hbx.symm))
  congr 1
  exact triple_eq_of_sum_of_two x y i j hij (hax.symm.trans hay) (hbx.symm.trans hby)
    (hx.trans hy.symm)

variable {m : ℕ} [NeZero m]

 theorem base_codegree (lam : ZMod m) (S : Finset (ZMod m))
    (X : Finset (Fin 3 × ZMod m)) (hX : X.card = 2) : codegree (baseGraph lam S) X ≤ 1 := by
  apply constant_sum_codegree _ 0 _ X hX
  intro e he
  obtain ⟨s, hs, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  refine ⟨fun j => baseMap lam s.val j a, rfl, ?_⟩
  simp [Fin.sum_univ_three, baseMap]
  ring

 theorem double_fixed_codegree (lam δ : ZMod m) (S : Finset (ZMod m)) (h : Bool)
    (X : Finset (Fin 3 × ZMod m)) (hX : X.card = 2) :
    codegree (coordinateHypergraph (fun s : S => doubleMap lam δ h s.val)) X ≤ 1 := by
  apply constant_sum_codegree _ (δ * (bit h : ZMod m)) _ X hX
  intro e he
  obtain ⟨s, hs, he⟩ := Finset.mem_biUnion.mp he
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
  refine ⟨fun j => doubleMap lam δ h s.val j a, rfl, ?_⟩
  rw [Fin.sum_univ_three]
  exact double_sum lam δ a s.val h

 theorem double_codegree (lam δ : ZMod m) (S : Finset (ZMod m))
    (X : Finset (Fin 3 × ZMod m)) (hX : X.card = 2) :
    codegree (coordinateHypergraph (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val)) X ≤ 2 := by
  let G := fun h => coordinateHypergraph (fun s : S => doubleMap lam δ h s.val)
  have heq : coordinateHypergraph (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val) =
      G false ∪ G true := by
    ext e
    simp only [G, coordinateHypergraph, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_union]
    constructor
    · rintro ⟨⟨h, s⟩, he⟩
      cases h
      · exact Or.inl ⟨s, he⟩
      · exact Or.inr ⟨s, he⟩
    · rintro (⟨s, he⟩ | ⟨s, he⟩)
      · exact ⟨(false, s), he⟩
      · exact ⟨(true, s), he⟩
  rw [heq, codegree, Finset.filter_union]
  exact (Finset.card_union_le _ _).trans
    (by have h0 := double_fixed_codegree lam δ S false X hX
        have h1 := double_fixed_codegree lam δ S true X hX
        change codegree (G false) X + codegree (G true) X ≤ 2
        dsimp [G]
        omega)

/-- Full constant-sum doubling statement, including ordinary uniformity,
balance, rigidity, and maximum pair codegree two. -/
 theorem Seed.doubling {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hm : 3 ≤ m) (hodd : Odd m) (δ : ZMod m) (hδ : IsUnit δ) :
    ∃ H : Hypergraph (Fin 3 × ZMod m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H (2 * S.card) ∧ maxDegree H 2 ≤ 2 := by
  let H := coordinateHypergraph (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val)
  refine ⟨H, ?_, ?_, ?_, ?_⟩
  · simpa using coordinateHypergraph_uniform (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val)
  · simpa using coordinateHypergraph_balanced (fun hs : Bool × S => doubleMap lam δ hs.1 hs.2.val)
  · let e : Fin (2 * S.card) ≃ (Bool × S) :=
      (Fintype.equivFinOfCardEq (by simp)).symm
    exact ⟨(B.doubledFamily hm hodd δ hδ).reindex e⟩
  · exact maxDegree_le H 2 2 (double_codegree lam δ S)

end RigidGHZ.Supplement.Affine
