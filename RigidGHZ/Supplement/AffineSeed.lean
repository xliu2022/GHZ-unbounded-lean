module

public import RigidGHZ.Partite
public import RigidGHZ.Supplement.MarkedCounts
public import Mathlib.Algebra.Group.Units.Equiv
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Ring

/-! The finite affine seed hypothesis, stated for ordinary hypergraphs.
The first part has coordinate `a`, the second `lam*a+s`, and the third
`-(lam+1)*a-s`, exactly as in the supplement. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- The actual affine coordinate rows of a single-sum seed. -/
def baseMap (lam s : ZMod m) : Fin 3 → ZMod m → ZMod m :=
  ![id, (fun a => lam * a + s), (fun a => -(lam + 1) * a - s)]

/-- The simple ordinary tripartite hypergraph of all seed rows. -/
def baseGraph (lam : ZMod m) (S : Finset (ZMod m)) : Hypergraph (Fin 3 × ZMod m) :=
  coordinateHypergraph (fun s : S => baseMap lam s.val)

/-- This is the sole finite seed hypothesis. Completeness is about standard
perfect matchings of the ordinary affine hypergraph, not about a surrogate test. -/
structure Seed (lam : ZMod m) (S : Finset (ZMod m)) : Prop where
  unit_left : IsUnit lam
  unit_right : IsUnit (lam + 1)
  complete : ∀ M, PerfectMatching (baseGraph lam S) M →
    ∃ s : S, M = coordinateMatching (baseMap lam s.val)

 theorem baseMap_bijective {lam : ZMod m} (hlam : IsUnit lam) (hlam1 : IsUnit (lam + 1))
    (s : ZMod m) (j : Fin 3) : Function.Bijective (baseMap lam s j) := by
  fin_cases j
  · exact Function.bijective_id
  · obtain ⟨u, hu⟩ := hlam
    simpa [baseMap, Function.comp_def, hu] using
      (Equiv.addRight s).bijective.comp u.mulLeft_bijective
  · obtain ⟨u, hu⟩ := hlam1
    have hf : (fun a : ZMod m => -(lam + 1) * a - s) =
        (fun a : ZMod m => -((u : ZMod m) * a) + -s) := by
      funext a
      rw [hu]
      ring
    change Function.Bijective (fun a : ZMod m => -(lam + 1) * a - s)
    rw [hf]
    exact (Equiv.addRight (-s)).bijective.comp
      ((Equiv.neg (ZMod m)).bijective.comp u.mulLeft_bijective)

/-- Coordinate permutations without changing the printed affine formulas. -/
def basePerm {lam : ZMod m} (hlam : IsUnit lam) (hlam1 : IsUnit (lam + 1))
    (s : ZMod m) (j : Fin 3) : Equiv.Perm (ZMod m) :=
  Equiv.ofBijective (baseMap lam s j) (baseMap_bijective hlam hlam1 s j)

@[simp] theorem basePerm_apply {lam : ZMod m} (hlam : IsUnit lam) (hlam1 : IsUnit (lam + 1))
    (s : ZMod m) (j : Fin 3) (a : ZMod m) :
    basePerm hlam hlam1 s j a = baseMap lam s j a := rfl

 theorem base_separate (lam : ZMod m) {s t : ZMod m} (hst : s ≠ t) (a : ZMod m) :
    baseMap lam s 1 a ≠ baseMap lam t 1 a := by
  simpa [baseMap] using hst

/-- A finite affine seed gives its prescribed rigid matching family. -/
def Seed.family {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S) :
    RigidFamily (baseGraph lam S) S where
  matching s := coordinateMatching (baseMap lam s.val)
  perfect s := (coordinateMatching_perfect (baseMap lam s.val)
    (baseMap_bijective B.unit_left B.unit_right s.val)).mono (by
      intro e he
      exact Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, he⟩)
  edge_disjoint := by
    intro s t hst
    apply Finset.disjoint_left.mpr
    intro e hes het
    obtain ⟨a, ha, hea⟩ := Finset.mem_image.mp hes
    obtain ⟨b, hb, heb⟩ := Finset.mem_image.mp het
    have h := tupleEdge_injective (hea.trans heb.symm)
    have hab : a = b := by simpa [baseMap] using congrFun h 0
    subst b
    have hst' : s.val = t.val := by simpa [baseMap] using congrFun h 1
    exact hst (Subtype.ext hst')
  covers := rfl
  complete := B.complete

/-- The finite seed hypothesis implies the coordinate uniqueness used by the
cyclic construction, through the ordinary perfect-matching bridge. -/
 theorem Seed.coordinate_complete {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (q r : Equiv.Perm (ZMod m))
    (hlocal : ∀ a, ∃ s : S, q a = lam * a + s.val ∧ r a = -(lam + 1) * a - s.val) :
    ∃ s : S, (∀ a, q a = lam * a + s.val) ∧ (∀ a, r a = -(lam + 1) * a - s.val) := by
  let p : Fin 3 → Equiv.Perm (ZMod m) := ![Equiv.refl _, q, r]
  let M := coordinateMatching (fun j a => p j a)
  have hM : PerfectMatching (baseGraph lam S) M := by
    apply (coordinateMatching_perfect (fun j a => p j a) (fun j => (p j).bijective)).mono
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨s, hq, hr⟩ := hlocal a
    apply Finset.mem_biUnion.mpr
    refine ⟨s, Finset.mem_univ _, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, ?_⟩⟩
    congr 1
    funext j
    fin_cases j <;> simp [p, baseMap, hq, hr]
  obtain ⟨s, hs⟩ := B.complete M hM
  have hp : p = basePerm B.unit_left B.unit_right s.val :=
    coordinates_eq_of_matching_eq 0 p (basePerm B.unit_left B.unit_right s.val)
      rfl (by ext a; rfl) hs
  refine ⟨s, ?_, ?_⟩
  · intro a
    have h := congrArg (fun z : Fin 3 → Equiv.Perm (ZMod m) => z 1 a) hp
    exact h
  · intro a
    have h := congrArg (fun z : Fin 3 → Equiv.Perm (ZMod m) => z 2 a) hp
    exact h

 theorem sum_zmod_eq_zero (hodd : Odd m) : ∑ a : ZMod m, a = 0 := by
  have hneg : - ∑ a : ZMod m, a = ∑ a : ZMod m, a := by
    simpa [← Finset.sum_neg_distrib] using Equiv.sum_comp (Equiv.neg (ZMod m)) (fun a => a)
  have htwo : (2 : ZMod m) * (∑ a : ZMod m, a) = 0 := by
    rw [two_mul, ← neg_eq_iff_add_eq_zero]
    exact hneg
  have hu : IsUnit (2 : ZMod m) := (ZMod.isUnit_iff_coprime 2 m).mpr hodd.coprime_two_left
  exact hu.mul_left_cancel (by simpa using htwo)

end RigidGHZ.Supplement.Affine
