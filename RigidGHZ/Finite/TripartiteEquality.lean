module

public import RigidGHZ.Finite.TripartiteUpper
public import Mathlib.Data.Fintype.EquivFin

@[expose] public section
namespace RigidGHZ.Finite
open scoped BigOperators

/- Equality in the finite exchange inequality forces all three completion
counts to equal two. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
 theorem three_exchange_weight_equality :
    ∀ R : Fin 3 → Fin 3 → Bool,
      (∀ a, R a a = true) →
      (∀ a b, a ≠ b → ¬(R a b = true ∧ R b a = true)) →
      (∑ a : Fin 3, 6 / (Finset.univ.filter (fun b => R a b = true)).card) = 9 →
      ∀ a, (Finset.univ.filter (fun b => R a b = true)).card = 2 := by
  decide

section Equality
variable {H : Hypergraph (Fin 3 × Fin 3)}

/-- When there are six matchings, equality holds in every local exchange bound. -/
theorem extremal_local_weights (F : RigidFamily H (Fin 6))
    (p : Fin 6 → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w)) :
    (∀ i, (∑ a : Fin 3, 6 / (Finset.univ.filter
      (fun x : Fin 6 × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card) = 9) ∧
    (∑ x : Fin 6 × Fin 3, 6 / (Finset.univ.filter
      (fun y : Fin 6 × Fin 3 => coordinatePair p y = coordinatePair p x)).card) = 54 := by
  classical
  let w : Fin 6 → ℕ := fun i => ∑ a : Fin 3, 6 / (Finset.univ.filter
      (fun x : Fin 6 × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card
  have hlo : ∀ i ∈ (Finset.univ : Finset (Fin 6)), 9 ≤ w i := by
    intro i hi
    exact coordinate_local_weight F p hp0 hm i
  have hsumlo := Finset.sum_le_sum hlo
  have hsumhi := pair_fiber_weight_bound (coordinatePair p)
  rw [Fintype.sum_prod_type] at hsumhi
  have hc : (∑ _i : Fin 6, (9 : ℕ)) = 54 := by decide
  have heq : (∑ _i : Fin 6, (9 : ℕ)) = ∑ i, w i := by
    rw [hc]
    rw [hc] at hsumlo
    exact Nat.le_antisymm hsumlo hsumhi
  have heach := (Finset.sum_eq_sum_iff_of_le hlo).mp heq
  constructor
  · intro i
    exact (heach i (Finset.mem_univ _)).symm
  · rw [Fintype.sum_prod_type]
    exact heq.symm.trans hc

/-- Every pair fiber meeting a source has size exactly two. -/
theorem extremal_source_fiber_two (F : RigidFamily H (Fin 6))
    (p : Fin 6 → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (i : Fin 6) (a : Fin 3) :
    (Finset.univ.filter (fun x : Fin 6 × Fin 3 =>
      coordinatePair p x = coordinatePair p (i,a))).card = 2 := by
  classical
  let R : Fin 3 → Fin 3 → Bool := fun a b =>
    decide (∃ j, coordinatePair p (j,b) = coordinatePair p (i,a))
  have hd : ∀ a, R a a = true := by
    intro a
    simp only [R, decide_eq_true_eq]
    exact ⟨i, rfl⟩
  have ha : ∀ a b, a ≠ b → ¬(R a b = true ∧ R b a = true) := by
    intro a b hab
    simpa only [R, decide_eq_true_eq] using coordinate_exchange_antisymm F p hp0 hm i a b hab
  have hc : ∀ a : Fin 3,
      (Finset.univ.filter (fun x : Fin 6 × Fin 3 => coordinatePair p x = coordinatePair p (i,a))).card =
      (Finset.univ.filter (fun b => R a b = true)).card := by
    intro a
    convert pair_fiber_card F p hp0 hm i a using 1
    congr 1
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, R, decide_eq_true_eq]
  have hw : (∑ a : Fin 3, 6 / (Finset.univ.filter (fun b => R a b = true)).card) = 9 := by
    simpa only [← hc] using (extremal_local_weights F p hp0 hm).1 i
  exact (hc a).trans (three_exchange_weight_equality R hd ha hw a)

/-- Every one of the nine cross-part pairs has exactly two source completions. -/
theorem extremal_pair_fiber_two (F : RigidFamily H (Fin 6))
    (p : Fin 6 → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (z : Fin 3 × Fin 3) :
    (Finset.univ.filter (fun x : Fin 6 × Fin 3 => coordinatePair p x = z)).card = 2 := by
  classical
  let c : Fin 3 × Fin 3 → ℕ := fun z =>
    (Finset.univ.filter (fun x : Fin 6 × Fin 3 => coordinatePair p x = z)).card
  have hs := Finset.sum_fiberwise' (Finset.univ : Finset (Fin 6 × Fin 3))
    (coordinatePair p) (fun z => 6 / c z)
  have hs' : (∑ z : Fin 3 × Fin 3, c z * (6 / c z)) = 54 := by
    have h54 := (extremal_local_weights F p hp0 hm).2
    have heq : (∑ z : Fin 3 × Fin 3, c z * (6 / c z)) =
        ∑ x : Fin 6 × Fin 3, 6 / c (coordinatePair p x) := by
      simpa only [Finset.sum_const, smul_eq_mul] using hs
    exact heq.trans h54
  have hb : ∀ z ∈ (Finset.univ : Finset (Fin 3 × Fin 3)), c z * (6 / c z) ≤ 6 :=
    fun z _ => Nat.mul_div_le 6 _
  have heq : (∑ z : Fin 3 × Fin 3, c z * (6 / c z)) = ∑ _z : Fin 3 × Fin 3, 6 := by
    simpa using hs'
  have hz := (Finset.sum_eq_sum_iff_of_le hb).mp heq z (Finset.mem_univ _)
  have hcpos : 0 < c z := by
    by_contra h
    have hc0 : c z = 0 := by omega
    simp only [hc0, Nat.div_zero, Nat.zero_mul] at hz
    omega
  obtain ⟨⟨i,a⟩, hia⟩ := Finset.card_pos.mp hcpos
  have hpair := (Finset.mem_filter.mp hia).2
  simpa only [hpair] using extremal_source_fiber_two F p hp0 hm i a

/-- Membership of a transversal edge is equivalent to a prescribed source with
its first coordinate and remaining pair. -/
theorem edge_mem_iff_source_pair (F : RigidFamily H (Fin 6))
    (p : Fin 6 → Fin 3 → Equiv.Perm (Fin 3))
    (hp0 : ∀ i, p i 0 = Equiv.refl (Fin 3))
    (hm : ∀ i, F.matching i = coordinateMatching (fun t w => p i t w))
    (a b c : Fin 3) :
    tupleEdge ![a,b,c] ∈ H ↔ ∃ i, coordinatePair p (i,a) = (b,c) := by
  constructor
  · intro he
    obtain ⟨i, hi⟩ := F.mem_iff.mp he
    rw [hm] at hi
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hi
    have hcoords := tupleEdge_injective heq
    have hwa : w = a := by
      have h0 := congrFun hcoords 0
      simpa [hp0] using h0
    subst w
    refine ⟨i, Prod.ext ?_ ?_⟩
    · exact congrFun hcoords 1
    · exact congrFun hcoords 2
  · rintro ⟨i, hi⟩
    have heq : coordinateSource p (i,a) = ![a,b,c] := by
      funext t
      fin_cases t
      · change (p i 0) a = a
        simp [hp0]
      · exact congrArg Prod.fst hi
      · exact congrArg Prod.snd hi
    rw [← heq]
    exact (F.perfect i).subset (source_mem_matching F p hm (i,a))

end Equality

/-- Equality in the sharp tripartite bound forces every pair from the last two
parts to have exactly two completions in the first part. -/
theorem extremal_first_codegree_two {H : Hypergraph (Fin 3 × Fin 3)}
    (htrans : ∀ e ∈ H, ∃ x : Fin 3 → Fin 3, e = tupleEdge x)
    (hR : IsRigid H 6) (b c : Fin 3) :
    (Finset.univ.filter (fun a : Fin 3 => tupleEdge ![a,b,c] ∈ H)).card = 2 := by
  classical
  obtain ⟨F⟩ := hR
  have hex : ∀ i : Fin 6, ∃ q : Fin 3 → Equiv.Perm (Fin 3),
      q 0 = Equiv.refl (Fin 3) ∧ F.matching i = coordinateMatching (fun t w => q t w) := by
    intro i
    exact perfectMatching_coordinates 0 htrans (F.perfect i)
  choose p hp0 hm using hex
  have hcount := extremal_pair_fiber_two F p hp0 hm (b,c)
  have hcpos : 0 < (Finset.univ.filter (fun x : Fin 6 × Fin 3 => coordinatePair p x = (b,c))).card := by
    omega
  obtain ⟨⟨i,a⟩, hia⟩ := Finset.card_pos.mp hcpos
  have hpair := (Finset.mem_filter.mp hia).2
  have hcard := pair_fiber_card F p hp0 hm i a
  rw [hpair] at hcard
  have heq : (Finset.univ.filter (fun a : Fin 3 => tupleEdge ![a,b,c] ∈ H)) =
      Finset.univ.filter (fun a : Fin 3 => ∃ i, coordinatePair p (i,a) = (b,c)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, edge_mem_iff_source_pair F p hp0 hm]
  rw [heq]
  have heqcard : (Finset.univ.filter (fun a : Fin 3 => ∃ i, coordinatePair p (i,a) = (b,c))).card =
      (Finset.univ.filter (fun x : Fin 6 × Fin 3 => coordinatePair p x = (b,c))).card := by
    convert hcard.symm using 1
    congr 1
    ext t
    simp
  exact heqcard.trans hcount

end RigidGHZ.Finite
