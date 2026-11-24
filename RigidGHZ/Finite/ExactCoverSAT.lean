module

public import RigidGHZ.Basic
public import RigidGHZ.Finite.SatKernel

/-! A sound propositional certificate for completeness of an explicit list of
perfect matchings. Variables denote membership of actual hyperedges in an
arbitrary ordinary perfect matching. Positive clauses cover vertices, negative
pairs forbid overlapping distinct edges, and one negative clause excludes each
prescribed matching. A refutation therefore proves ordinary completeness. -/

@[expose] public section
namespace RigidGHZ.Finite

structure ExactCoverData (V : Type*) [DecidableEq V] (n e d : ℕ) where
  vertex : Fin n → V
  edge : Fin e → Finset V
  through : Fin n → List (Fin e)
  row : Fin d → List (Fin e)

namespace ExactCoverData

variable {V : Type*} [DecidableEq V] {n e d : ℕ}

def host (D : ExactCoverData V n e d) : Hypergraph V := Finset.univ.image D.edge

def matching (D : ExactCoverData V n e d) (r : Fin d) : Hypergraph V :=
  (D.row r).toFinset.image D.edge

def valuation (D : ExactCoverData V n e d) (M : Hypergraph V) (j : ℕ) : Prop :=
  if hj : j < e then D.edge ⟨j,hj⟩ ∈ M else False

@[simp] theorem valuation_edge (D : ExactCoverData V n e d) (M : Hypergraph V)
    (i : Fin e) : D.valuation M i.val ↔ D.edge i ∈ M := by
  simp only [valuation, dif_pos i.isLt]

end ExactCoverData

structure ExactCoverValid {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) : Prop where
  uniform : ∀ i, (D.edge i).card = 3
  injective : Function.Injective D.edge
  through_complete : ∀ v i, D.vertex v ∈ D.edge i → i ∈ D.through v
  perfect : ∀ r, PerfectMatching D.host (D.matching r)
  disjoint : Pairwise (fun r s => Disjoint (D.matching r) (D.matching s))
  covers : D.host = Finset.univ.biUnion D.matching

namespace ExactCoverValid

variable {V : Type*} [DecidableEq V] {n e d : ℕ}
    {D : ExactCoverData V n e d}

theorem host_uniform (C : ExactCoverValid D) : Uniform D.host 3 := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact C.uniform i

theorem edge_nonempty (C : ExactCoverValid D) {a : Finset V} (ha : a ∈ D.host) :
    a.Nonempty := by
  apply Finset.card_pos.mp
  rw [C.host_uniform a ha]
  decide

noncomputable def family (C : ExactCoverValid D)
    (complete : ∀ M, PerfectMatching D.host M → ∃ r, M = D.matching r) :
    RigidFamily D.host (Fin d) where
  matching := D.matching
  perfect := C.perfect
  edge_disjoint := C.disjoint
  covers := C.covers
  complete := complete

end ExactCoverValid

theorem sat_negative_list {v : Sat.Valuation} {xs : List ℕ}
    (h : ∃ i ∈ xs, ¬ v i) : v.satisfies (xs.map Sat.Literal.neg) := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    intro ha
    obtain ⟨i,hi,hv⟩ := h
    rcases List.mem_cons.mp hi with rfl | hi
    · exact False.elim (hv ha)
    · exact ih ⟨i,hi,hv⟩

theorem exactCover_cover {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) (C : ExactCoverValid D)
    (M : Hypergraph V) (hM : PerfectMatching D.host M) (v : Fin n) :
    Sat.Valuation.satisfies (D.valuation M)
      (((D.through v).map Fin.val).map Sat.Literal.pos) := by
  obtain ⟨a,ha,_⟩ := hM.existsUnique_edge (D.vertex v)
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (hM.subset ha.1)
  apply sat_positive_list
  exact ⟨i.val,List.mem_map.mpr ⟨i,C.through_complete v i ha.2,rfl⟩,
    (D.valuation_edge M i).mpr ha.1⟩

theorem exactCover_conflict {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) (C : ExactCoverValid D)
    (M : Hypergraph V) (hM : PerfectMatching D.host M)
    (i j : Fin e) (v : Fin n)
    (h : i ≠ j ∧ D.vertex v ∈ D.edge i ∧ D.vertex v ∈ D.edge j) :
    Sat.Valuation.satisfies (D.valuation M) [Sat.Literal.neg i.val,Sat.Literal.neg j.val] := by
  intro hi hj
  have hdis := hM.disjoint_edges ((D.valuation_edge M i).mp hi)
    ((D.valuation_edge M j).mp hj) (fun heq => h.1 (C.injective heq))
  exact Finset.disjoint_left.mp hdis h.2.1 h.2.2

theorem exactCover_exclude {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) (C : ExactCoverValid D)
    (M : Hypergraph V) (hM : PerfectMatching D.host M)
    (hne : ∀ r, M ≠ D.matching r) (r : Fin d) :
    Sat.Valuation.satisfies (D.valuation M) (((D.row r).map Fin.val).map Sat.Literal.neg) := by
  classical
  apply sat_negative_list
  by_contra hn
  push_neg at hn
  have hsub : D.matching r ⊆ M := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp ha
    apply (D.valuation_edge M i).mp
    exact hn i.val (List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩)
  have heq := (C.perfect r).eq_of_subset hM hsub
    (fun a ha => C.edge_nonempty (hM.subset ha))
  exact hne r heq.symm

end RigidGHZ.Finite
