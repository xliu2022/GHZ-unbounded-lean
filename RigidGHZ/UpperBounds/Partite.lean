module

public import RigidGHZ.UpperBounds.Reciprocal
public import RigidGHZ.Relabel
public import Mathlib.Data.Fintype.Pi

/-!
# The balanced multipartite harmonic upper bound

We use canonical tuple coordinates, but all rigidity hypotheses refer to the
ordinary finite hypergraph and its actual perfect matchings.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

variable {A W I : Type*} [Fintype A] [DecidableEq A]
  [Fintype W] [DecidableEq W] [Fintype I]

/-- Forget the distinguished part of a transversal. -/
def tupleProjection (a0 : A) (x : A → W) : {a : A // a ≠ a0} → W := fun a => x a

/-- All tuples whose transversal edge is present in the ordinary hypergraph. -/
def tupleArrays (H : Hypergraph (A × W)) : Finset (A → W) :=
  Finset.univ.filter (fun x => tupleEdge x ∈ H)

@[simp] theorem mem_tupleArrays {H : Hypergraph (A × W)} {x : A → W} :
    x ∈ tupleArrays H ↔ tupleEdge x ∈ H := by simp [tupleArrays]

/-- Replace only the distinguished coordinate of a matching row. -/
def replacedTuple (a0 : A) (p : A → Equiv.Perm W) (u v : W) (a : A) : W :=
  if a = a0 then v else p a u

@[simp] theorem replacedTuple_at (a0 : A) (p : A → Equiv.Perm W) (u v : W) :
    replacedTuple a0 p u v a0 = v := by simp [replacedTuple]

@[simp] theorem replacedTuple_away (a0 : A) (p : A → Equiv.Perm W)
    (u v : W) {a : A} (ha : a ≠ a0) : replacedTuple a0 p u v a = p a u := by
  simp [replacedTuple, ha]

theorem replacedTuple_self (a0 : A) (p : A → Equiv.Perm W)
    (hp0 : p a0 = Equiv.refl W) (u : W) :
    replacedTuple a0 p u u = fun a => p a u := by
  funext a
  by_cases ha : a = a0
  · subst a
    simp [hp0]
  · simp [ha]

@[simp] theorem tupleProjection_replaced (a0 : A) (p : A → Equiv.Perm W)
    (u v : W) : tupleProjection a0 (replacedTuple a0 p u v) =
      tupleProjection a0 (fun a => p a u) := by
  funext a
  exact replacedTuple_away a0 p u v a.2

/-- The loopless exchange digraph, now indexed by the first coordinate. -/
def tupleExchangeArc (H : Hypergraph (A × W)) (a0 : A)
    (p : A → Equiv.Perm W) (u v : W) : Prop :=
  u ≠ v ∧ tupleEdge (replacedTuple a0 p u v) ∈ H

instance (H : Hypergraph (A × W)) (a0 : A) (p : A → Equiv.Perm W) :
    DecidableRel (tupleExchangeArc H a0 p) := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ tupleEdge (replacedTuple a0 p u v) ∈ H))

/-- Coordinate exchanges inherit the no-proper-cycle obstruction from a standard rigid family. -/
theorem tupleExchange_noPartialPermutations {H : Hypergraph (A × W)}
    (G : RigidFamily H I) (i : I) (a0 a1 : A) (ha : a1 ≠ a0)
    (p : A → Equiv.Perm W) (hp0 : p a0 = Equiv.refl W)
    (hmatching : G.matching i = coordinateMatching (fun a w => p a w)) :
    NoPartialPermutations (tupleExchangeArc H a0 p) := by
  classical
  letI : Nonempty A := ⟨a0⟩
  intro q hq hfixed
  let p' : A → Equiv.Perm W := fun a => if a = a0 then q else p a
  have hrow : ∀ w, (fun a => p' a w) = replacedTuple a0 p w (q w) := by
    intro w
    funext a
    by_cases ha : a = a0 <;> simp [p', replacedTuple, ha]
  have hsub : coordinateMatching (fun a w => p' a w) ⊆ H := by
    intro e he
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp he
    rw [hrow]
    rcases hq w with hfix | harc
    · rw [hfix, replacedTuple_self a0 p hp0]
      apply (G.perfect i).subset
      rw [hmatching]
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    · exact harc.2
  have hN := (coordinateMatching_perfect (fun a w => p' a w)
    (fun a => (p' a).bijective)).mono hsub
  obtain ⟨j, hj⟩ := G.complete _ hN
  obtain ⟨w, hw⟩ := hfixed
  have hbase : tupleEdge (fun a => p a w) ∈ G.matching i := by
    rw [hmatching]
    exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
  have hother : tupleEdge (fun a => p a w) ∈ G.matching j := by
    rw [← hj]
    apply Finset.mem_image.mpr
    refine ⟨w, Finset.mem_univ _, ?_⟩
    rw [hrow, hw, replacedTuple_self a0 p hp0]
  have hij : i = j := G.eq_of_shared_edge hbase hother
  have hNeq : coordinateMatching (fun a w => p' a w) =
      coordinateMatching (fun a w => p a w) := by
    rw [← hmatching, hij]
    exact hj
  apply Equiv.ext
  intro u
  have he : tupleEdge (fun a => p' a u) ∈ coordinateMatching (fun a w => p a w) := by
    rw [← hNeq]
    exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
  obtain ⟨v, hv, htuple⟩ := Finset.mem_image.mp he
  have hcoords := tupleEdge_injective htuple
  have huv : v = u := by
    apply (p a1).injective
    simpa [p', ha] using congrFun hcoords a1
  have h0 := congrFun hcoords a0
  simpa [p', hp0, huv] using h0.symm

/-- Inclusive neighbor count equals the fiber size of the projection. -/
theorem tupleExchange_fiber_card {H : Hypergraph (A × W)}
    (a0 : A) (p : A → Equiv.Perm W) (hp0 : p a0 = Equiv.refl W)
    (hrow : ∀ u, tupleEdge (fun a => p a u) ∈ H) (u : W) :
    1 + (Finset.univ.filter (tupleExchangeArc H a0 p u)).card =
      ((tupleArrays H).filter (fun x => tupleProjection a0 x =
        tupleProjection a0 (fun a => p a u))).card := by
  classical
  let N : Finset W := Finset.univ.filter (fun v => tupleEdge (replacedTuple a0 p u v) ∈ H)
  have hu : u ∈ N := by
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and,
      replacedTuple_self a0 p hp0]
    exact hrow u
  have harc : Finset.univ.filter (tupleExchangeArc H a0 p u) = N.erase u := by
    ext v
    simp [N, tupleExchangeArc, and_comm, and_left_comm, eq_comm]
  have hN : N.card = ((tupleArrays H).filter (fun x => tupleProjection a0 x =
        tupleProjection a0 (fun a => p a u))).card := by
    apply Finset.card_bij (fun v _ => replacedTuple a0 p u v)
    · intro v hv
      exact Finset.mem_filter.mpr
        ⟨mem_tupleArrays.mpr (Finset.mem_filter.mp hv).2, tupleProjection_replaced _ _ _ _⟩
    · intro v hv w hw heq
      have he := congrFun heq a0
      simpa using he
    · intro x hx
      have hproj := (Finset.mem_filter.mp hx).2
      have heq : replacedTuple a0 p u (x a0) = x := by
        funext a
        by_cases ha : a = a0
        · subst a
          simp
        · exact (replacedTuple_away a0 p u (x a0) ha).trans
            (congrFun hproj ⟨a, ha⟩).symm
      refine ⟨x a0, ?_, heq⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [heq]
      exact mem_tupleArrays.mp (Finset.mem_filter.mp hx).1
  rw [harc, ← hN, Nat.add_comm, Finset.card_erase_add_one hu]

/-- Summing inverse fiber sizes counts the distinct projected objects. -/
theorem sum_inverse_fiber_card {E P : Type*} [DecidableEq E] [DecidableEq P]
    (s : Finset E) (f : E → P) :
    (∑ e ∈ s, 1 / (((s.filter (fun x => f x = f e)).card : ℕ) : ℝ)) =
      ((s.image f).card : ℝ) := by
  classical
  have hsum := Finset.sum_fiberwise_of_maps_to
    (s := s) (t := s.image f) (g := f) (fun e he => Finset.mem_image.mpr ⟨e, he, rfl⟩)
    (fun e => (1 : ℝ) / (s.filter (fun x => f x = f e)).card)
  rw [← hsum]
  have hfiber : ∀ y ∈ s.image f,
      (∑ e ∈ s.filter (fun e => f e = y),
        (1 : ℝ) / (s.filter (fun x => f x = f e)).card) = 1 := by
    intro y hy
    have hcard : (s.filter (fun e => f e = y)).card ≠ 0 := by
      obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.card_ne_zero.mpr ⟨e, Finset.mem_filter.mpr ⟨he, rfl⟩⟩
    calc
      _ = ∑ _e ∈ s.filter (fun e => f e = y),
          (1 : ℝ) / (s.filter (fun x => f x = y)).card := by
        apply Finset.sum_congr rfl
        intro e he
        rw [(Finset.mem_filter.mp he).2]
      _ = 1 := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        exact mul_one_div_cancel (Nat.cast_ne_zero.mpr hcard)
  exact (Finset.sum_congr rfl hfiber).trans (by simp)

/-- The harmonic bound by the number of distinct projections, for arbitrary
standard rigid hypergraphs whose edges are transversals. -/
theorem tuple_partite_harmonic_shadow {H : Hypergraph (A × W)}
    (G : RigidFamily H I) (a0 a1 : A) (ha : a1 ≠ a0)
    (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x) :
    (Fintype.card I : ℝ) * beta (Fintype.card W) ≤
      (((tupleArrays H).image (tupleProjection a0)).card : ℝ) := by
  classical
  have hp : ∀ i : I, ∃ p : A → Equiv.Perm W,
      p a0 = Equiv.refl W ∧ G.matching i = coordinateMatching (fun a w => p a w) :=
    fun i => perfectMatching_coordinates a0 htrans (G.perfect i)
  choose p hp0 hmatching using hp
  let E := tupleArrays H
  let Ei : I → Finset (A → W) := fun i => Finset.univ.image (fun w a => p i a w)
  let weight : (A → W) → ℝ := fun x =>
    1 / (E.filter (fun y => tupleProjection a0 y = tupleProjection a0 x)).card
  have hmem : ∀ i x, x ∈ Ei i ↔ tupleEdge x ∈ G.matching i := by
    intro i x
    rw [hmatching]
    constructor
    · intro hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, rfl⟩
    · intro hx
      obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hx
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ _, tupleEdge_injective heq⟩
  have hE : E = Finset.univ.biUnion Ei := by
    ext x
    change x ∈ tupleArrays H ↔ x ∈ Finset.univ.biUnion Ei
    rw [mem_tupleArrays, G.mem_iff]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, hmem]
  have hdis : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint Ei := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro x hxi hxj
    exact Finset.disjoint_left.mp (G.edge_disjoint hij)
      ((hmem i x).mp hxi) ((hmem j x).mp hxj)
  have hinj : ∀ i, Function.Injective (fun w a => p i a w) := by
    intro i u v huv
    have hh := congrFun huv a0
    simpa only [hp0 i, Equiv.refl_apply] using hh
  have hbound : ∀ i, beta (Fintype.card W) ≤ ∑ x ∈ Ei i, weight x := by
    intro i
    have hrow : ∀ u, tupleEdge (fun a => p i a u) ∈ H := by
      intro u
      apply (G.perfect i).subset
      rw [hmatching]
      exact Finset.mem_image.mpr ⟨u, Finset.mem_univ _, rfl⟩
    have hb := reciprocal_outdegree_bound (tupleExchangeArc H a0 (p i))
      (fun w hw => hw.1 rfl)
      (tupleExchange_noPartialPermutations G i a0 a1 ha (p i) (hp0 i) (hmatching i))
    calc
      beta (Fintype.card W) ≤
          ∑ w : W, 1 / (1 + ((Finset.univ.filter (tupleExchangeArc H a0 (p i) w)).card : ℝ)) := hb
      _ = ∑ w : W, weight (fun a => p i a w) := by
        apply Finset.sum_congr rfl
        intro w _
        have hc := congrArg (fun n : ℕ => (1 : ℝ) / n)
          (tupleExchange_fiber_card a0 (p i) (hp0 i) hrow w)
        simpa only [Nat.cast_add, Nat.cast_one] using hc
      _ = ∑ x ∈ Ei i, weight x := by
        symm
        apply Finset.sum_image
        intro u hu v hv huv
        exact hinj i huv
  have hsum : (∑ i, ∑ x ∈ Ei i, weight x) = ∑ x ∈ E, weight x := by
    rw [hE, Finset.sum_biUnion hdis]
  have hb := Finset.sum_le_sum (s := (Finset.univ : Finset I)) (fun i _ => hbound i)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hsum] at hb
  exact hb.trans_eq (sum_inverse_fiber_card E (tupleProjection a0))

/-- At most `m^(r-1)` projections are possible for `r` parts of size `m`. -/
theorem tuple_projection_card_bound (H : Hypergraph (A × W)) (a0 : A) :
    ((tupleArrays H).image (tupleProjection a0)).card ≤
      Fintype.card W ^ (Fintype.card A - 1) := by
  have h := Finset.card_le_univ ((tupleArrays H).image (tupleProjection a0))
  have hA : Fintype.card {a : A // a ≠ a0} = Fintype.card A - 1 := by
    rw [Fintype.card_subtype]
    have hs : Finset.univ.filter (fun a : A => a ≠ a0) = Finset.univ.erase a0 := by
      ext a
      simp
    rw [hs, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
  simpa only [Fintype.card_fun, hA] using h

theorem tuple_partite_harmonic_bound {H : Hypergraph (A × W)}
    (G : RigidFamily H I) (a0 a1 : A) (ha : a1 ≠ a0)
    (htrans : ∀ e ∈ H, ∃ x : A → W, e = tupleEdge x) :
    (Fintype.card I : ℝ) * beta (Fintype.card W) ≤
      (Fintype.card W : ℝ) ^ (Fintype.card A - 1) := by
  have hb := tuple_partite_harmonic_shadow G a0 a1 ha htrans
  have hc := tuple_projection_card_bound H a0
  exact hb.trans (by exact_mod_cast hc)

/-- The multipartite numerical assertion of Theorem 4.1, on arbitrary vertex sets. -/
theorem balanced_partite_harmonic_bound {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d : ℕ} (hr : 2 ≤ r)
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    (d : ℝ) * beta m ≤ (m : ℝ) ^ (r - 1) := by
  obtain ⟨K, ⟨G⟩, htrans⟩ := hR.canonical hP
  let a0 : Fin r := ⟨0, by omega⟩
  let a1 : Fin r := ⟨1, by omega⟩
  have hne : a1 ≠ a0 := by
    intro h
    have hv := congrArg Fin.val h
    norm_num [a0, a1] at hv
  simpa only [Fintype.card_fin] using tuple_partite_harmonic_bound G a0 a1 hne htrans

end RigidGHZ.UpperBounds
