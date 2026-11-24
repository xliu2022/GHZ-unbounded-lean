module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Order.Lattice.Nat

/-!
# Explicit finite and infinite rigid-hypergraph families

These are the existence and threshold results of the Supplemental Material to
Heng Li and Xizhi Liu, *Unbounded GHZ dimension from fixed-order multiphoton
sources*. Every witness is an ordinary finite simple hypergraph and the stated
rigidity exhausts all its perfect matchings. Pair codegree and linearity have
their usual incidence meanings, specified below.

The three periodic families and the finite witnesses supply actual inputs for
grafting. The threshold statements quantify over every size in the stated
range; there is no hypothesis that a required finite seed exists. The linear
table is exactly 8→33, 9→62, 10→74, 11→112, 12→113.

The six-class and odd-size eight-class existence results use grafting proofs
instead of the paper's original uniform cyclic formulas. This statement does
not assert the locality properties of those original formulas.
-/

@[expose] public section

namespace RigidGHZ

/-- A finite simple hypergraph. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

/-- Every edge has `r` vertices. -/
def Uniform {V : Type*} (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A subset of the edges covering every vertex exactly once. -/
def PerfectMatching {V : Type*} [DecidableEq V] (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ ∀ v : V, (M.filter (fun e => v ∈ e)).card = 1

/-- Exhaustive edge-disjoint decomposition into prescribed perfect matchings. -/
structure RigidFamily {V : Type*} [DecidableEq V] (H : Hypergraph V)
    (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching
  complete : ∀ M, PerfectMatching H M → ∃ i, M = matching i

/-- Exactly the `d` prescribed matching classes, with no additional matching. -/
def IsRigid {V : Type*} [DecidableEq V] (H : Hypergraph V) (d : ℕ) : Prop :=
  Nonempty (RigidFamily H (Fin d))

/-- `r` equal vertex parts, each met once by every edge. -/
def BalancedPartite {V : Type*} [Fintype V] [DecidableEq V]
    (H : Hypergraph V) (r m : ℕ) : Prop :=
  ∃ color : V → Fin r,
    (∀ i, (Finset.univ.filter (fun v => color v = i)).card = m) ∧
    ∀ e ∈ H, ∀ i, (e.filter (fun v => color v = i)).card = 1

namespace UpperBounds

/-- Number of edges containing the given set. -/
def codegree {V : Type*} [DecidableEq V] (H : Hypergraph V) (S : Finset V) : ℕ :=
  (H.filter (fun e => S ⊆ e)).card

end UpperBounds

namespace Supplement

/-- Largest codegree of a `j`-element set, or zero if no such set exists. -/
def maxDegree {V : Type*} [Fintype V] [DecidableEq V] (H : Hypergraph V) (j : ℕ) : ℕ :=
  @Finset.sup ℕ (Finset V) (@Lattice.toSemilatticeSup ℕ Nat.instLattice) Nat.instOrderBot
    (Finset.univ.powersetCard j) (UpperBounds.codegree H)

/-- Two distinct edges intersect in at most one vertex. -/
def IsLinear {V : Type*} [DecidableEq V] (H : Hypergraph V) : Prop :=
  ∀ e ∈ H, ∀ f ∈ H, e ≠ f → (e ∩ f).card ≤ 1

/-- The pair bound is `c`; all other positive-order bounds are `d`. -/
def pairBounds (d c j : ℕ) : ℕ := if j = 2 then c else d

/-- Existence of an actual balanced rigid hypergraph with the listed bounds. -/
def BoundedRigid (r m d : ℕ) (b : ℕ → ℕ) : Prop :=
  ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H d ∧
    ∀ j : ℕ, 1 ≤ j → maxDegree H j ≤ b j

/-- The analogous existence assertion without a multipartite restriction. -/
def BoundedUnrestricted (r m d : ℕ) (b : ℕ → ℕ) : Prop :=
  ∃ H : Hypergraph (Fin (r * m)), Uniform H r ∧ IsRigid H d ∧
    ∀ j : ℕ, 1 ≤ j → maxDegree H j ≤ b j

/-- Six matching classes at every part size at least three. -/
theorem six_at_every_size (m : ℕ) (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 6 ∧ H.card = 6 * m ∧ maxDegree H 2 ≤ 2 := by sorry

/-- The higher-uniformity six-class baseline after dimension doubling. -/
theorem six_general (r m : ℕ) (hr : 3 ≤ r) (hm : 3 ≤ m) :
    ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧
      IsRigid H (3 * 2 ^ (r - 2)) := by sorry

namespace Affine

/-- Eight classes at every odd size at least five, strengthening the paper's
coprime-to-six size range. -/
theorem eight_odd (m : ℕ) (hm : 5 ≤ m) (hodd : Odd m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ maxDegree H 2 ≤ 2 := by sorry

end Affine

namespace Periodic

/-- Eleven classes on `9q` vertices for every positive period. -/
theorem eleven_bounded {q : ℕ} (hq : 0 < q) :
    BoundedUnrestricted 3 (3 * q) 11 (fun _ => 11) := by sorry

/-- Ten classes on `6q` vertices for every positive odd period. -/
theorem ten_bounded {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    BoundedUnrestricted 3 (2 * q) 10 (fun _ => 10) := by sorry

/-- The linear Latin family with part size `8q` at positive odd periods. -/
theorem latin_bounded {q : ℕ} (hq : 0 < q) (hodd : Odd q) :
    BoundedRigid 3 (8 * q) 8 (pairBounds 8 1) := by sorry

end Periodic

namespace Thresholds

/-- The sharp minimum over all matching sizes at least two is ten; at size
one the maximum is one. The extrema are expressed by witnesses and upper bounds. -/
theorem ten_threshold_sharp :
    (∀ m : ℕ, 2 ≤ m → ∃ H : Hypergraph (Fin (3 * m)), Uniform H 3 ∧ IsRigid H 10) ∧
    (∀ (H : Hypergraph (Fin 6)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 10) ∧
    (∀ (H : Hypergraph (Fin 3)) (d : ℕ), Uniform H 3 → IsRigid H d → d ≤ 1) := by sorry

/-- Eight classes, all part sizes at least seven, pair codegree at most two. -/
theorem balanced_eight (m : ℕ) (hm : 7 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ maxDegree H 2 ≤ 2 := by sorry

/-- Ten classes at every size at least31 and at every odd size at least17. -/
theorem balanced_ten (m : ℕ) (hm : 31 ≤ m ∨ Odd m ∧ 17 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 10 ∧ maxDegree H 2 ≤ 2 := by sorry

/-- Twelve classes at every size at least43 and at every odd size at least35. -/
theorem balanced_twelve (m : ℕ) (hm : 43 ≤ m ∨ Odd m ∧ 35 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 12 ∧ maxDegree H 2 ≤ 2 := by sorry

/-- Twelve classes for unrestricted triples on every `3m` vertices, `m≥21`. -/
theorem unrestricted_twelve (m : ℕ) (hm : 21 ≤ m) :
    ∃ H : Hypergraph (Fin (3 * m)), Uniform H 3 ∧ IsRigid H 12 := by sorry

end Thresholds

namespace LinearThresholds

/-- The five published linear thresholds. -/
def threshold : ℕ → ℕ
  | 8 => 33
  | 9 => 62
  | 10 => 74
  | 11 => 112
  | 12 => 113
  | _ => 0

/-- Every size above the selected threshold admits a linear balanced witness. -/
theorem linear_thresholds (t m : ℕ) (ht : t ∈ ({8, 9, 10, 11, 12} : Finset ℕ))
    (hm : threshold t ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H t ∧ IsLinear H := by sorry

end LinearThresholds
end Supplement

namespace Finite.Seeds

/-- The explicit twelve-class witness on twelve vertices. -/
theorem U12.witness : ∃ H : Hypergraph (Fin 12), Uniform H 3 ∧ IsRigid H 12 := by sorry
/-- The explicit ten-class witness on fifteen vertices. -/
theorem U15.witness : ∃ H : Hypergraph (Fin 15), Uniform H 3 ∧ IsRigid H 10 := by sorry
/-- The explicit thirteen-class witness on eighteen vertices. -/
theorem U18.witness : ∃ H : Hypergraph (Fin 18), Uniform H 3 ∧ IsRigid H 13 := by sorry
/-- The explicit ten-class witness on twenty-one vertices. -/
theorem U21.witness : ∃ H : Hypergraph (Fin 21), Uniform H 3 ∧ IsRigid H 10 := by sorry
/-- The explicit ten-class witness on twenty-four vertices. -/
theorem U24.witness : ∃ H : Hypergraph (Fin 24), Uniform H 3 ∧ IsRigid H 10 := by sorry

end Finite.Seeds
end RigidGHZ
