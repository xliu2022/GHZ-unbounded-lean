module

public import RigidGHZ.Basic
public import Mathlib.GroupTheory.Perm.Basic

/-!
# The exchange obstruction from rigidity

Choose one representative in each edge of a perfect matching. A permutation of
these representatives gives another perfect matching whenever all replacement
edges are available. Rigidity forces every nonidentity such permutation to
move every matching edge. This is the precise no-proper-cycle obstruction used
in the harmonic shadow bound.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

variable {V I : Type*} [DecidableEq V] [Fintype I] {H M : Hypergraph V}

/-- Replace the chosen vertex of a block by the representative of its successor. -/
def exchangeEdge (rep : M → V) (q : Equiv.Perm M) (e : M) : Finset V :=
  insert (rep (q e)) (e.1.erase (rep e))

/-- The edge family obtained by a simultaneous exchange of representatives. -/
def exchangeMatching (rep : M → V) (q : Equiv.Perm M) : Hypergraph V :=
  Finset.univ.image (exchangeEdge rep q)

@[simp] theorem mem_exchangeEdge (rep : M → V) (q : Equiv.Perm M)
    (e : M) (v : V) :
    v ∈ exchangeEdge rep q e ↔ v = rep (q e) ∨ v ≠ rep e ∧ v ∈ e.1 := by
  simp [exchangeEdge]

theorem matching_edge_eq_of_common (hM : PerfectMatching H M)
    {e f : M} {v : V} (he : v ∈ e.1) (hf : v ∈ f.1) : e = f := by
  apply Subtype.ext
  obtain ⟨g, hg, huniq⟩ := hM.existsUnique_edge v
  exact (huniq e.1 ⟨e.2, he⟩).trans (huniq f.1 ⟨f.2, hf⟩).symm

theorem representatives_injective (hM : PerfectMatching H M)
    (rep : M → V) (hrep : ∀ e, rep e ∈ e.1) : Function.Injective rep := by
  intro e f hef
  apply matching_edge_eq_of_common hM (hrep e)
  simpa only [hef] using hrep f

/-- Every representative permutation covers each vertex exactly once. -/
theorem exchangeMatching_perfect (hM : PerfectMatching H M)
    (rep : M → V) (hrep : ∀ e, rep e ∈ e.1) (q : Equiv.Perm M)
    (hsupported : ∀ e, exchangeEdge rep q e ∈ H) :
    PerfectMatching H (exchangeMatching rep q) := by
  classical
  have hindex : ∀ v : V, ∃! e : M, v ∈ e.1 := by
    intro v
    obtain ⟨e, he, hu⟩ := hM.existsUnique_edge v
    refine ⟨⟨e, he.1⟩, he.2, ?_⟩
    intro f hf
    exact Subtype.ext (hu f.1 ⟨f.2, hf⟩)
  have hrow : ∀ v : V, ∃! e : M, v ∈ exchangeEdge rep q e := by
    intro v
    obtain ⟨e, he, hu⟩ := hindex v
    by_cases hv : v = rep e
    · refine ⟨q.symm e, ?_, ?_⟩
      · simp only [mem_exchangeEdge, Equiv.apply_symm_apply]
        exact Or.inl hv
      · intro f hf
        rcases mem_exchangeEdge rep q f v |>.mp hf with hf | ⟨hne, hf⟩
        · have hqe : q f = e := hu _ (by simpa only [hf] using hrep (q f))
          exact q.injective (hqe.trans (q.apply_symm_apply e).symm)
        · have hfe : f = e := hu f hf
          exact False.elim (hne (hv.trans (congrArg rep hfe).symm))
    · refine ⟨e, (mem_exchangeEdge rep q e v).mpr (Or.inr ⟨hv, he⟩), ?_⟩
      intro f hf
      rcases mem_exchangeEdge rep q f v |>.mp hf with hf | ⟨hne, hf⟩
      · have hqe : q f = e := hu _ (by simpa only [hf] using hrep (q f))
        exact False.elim (hv (hf.trans (congrArg rep hqe)))
      · exact hu f hf
  apply PerfectMatching.of_existsUnique
  · intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact hsupported f
  · intro v
    obtain ⟨e, he, hu⟩ := hrow v
    refine ⟨exchangeEdge rep q e, ⟨Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩, he⟩, ?_⟩
    intro f hf
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp hf.1
    exact congrArg (exchangeEdge rep q) (hu g hf.2)

theorem exchangeEdge_of_fixed (rep : M → V) (hrep : ∀ e, rep e ∈ e.1)
    (q : Equiv.Perm M) (e : M) (he : q e = e) : exchangeEdge rep q e = e.1 := by
  simp only [exchangeEdge, he, Finset.insert_erase (hrep e)]

/-- If all exchanged edges belong to the original matching, no representative moves. -/
theorem exchangeMatching_eq_implies_eq_refl (hM : PerfectMatching H M)
    (rep : M → V) (hrep : ∀ e, rep e ∈ e.1)
    (hsize : ∀ e : M, 2 ≤ e.1.card) (q : Equiv.Perm M)
    (heq : exchangeMatching rep q = M) : q = Equiv.refl M := by
  classical
  apply Equiv.ext
  intro e
  have herase : (e.1.erase (rep e)).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_erase_of_mem (hrep e)]
    exact Nat.sub_pos_of_lt (hsize e)
  obtain ⟨v, hv⟩ := herase
  have hv0 := Finset.mem_erase.mp hv
  have hex : exchangeEdge rep q e ∈ M := by
    exact (Finset.subset_of_eq heq) (Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩)
  have hxe : exchangeEdge rep q e = e.1 := by
    exact congrArg Subtype.val (matching_edge_eq_of_common hM
      (e := ⟨exchangeEdge rep q e, hex⟩) (f := e)
      (Finset.mem_insert_of_mem hv) hv0.2)
  apply matching_edge_eq_of_common hM (hrep (q e))
  change rep (q e) ∈ e.1
  rw [← hxe]
  exact Finset.mem_insert_self _ _

/--
A supported exchange with a fixed edge is the identity. The hypotheses are the
ordinary hypergraph definition of rigidity, with no assumed cycle condition.
-/
theorem rigid_exchange_fixed_implies_identity (G : RigidFamily H I) (i : I)
    (rep : G.matching i → V) (hrep : ∀ e, rep e ∈ e.1)
    (hsize : ∀ e : G.matching i, 2 ≤ e.1.card)
    (q : Equiv.Perm (G.matching i))
    (hsupported : ∀ e, exchangeEdge rep q e ∈ H)
    (hfixed : ∃ e, q e = e) : q = Equiv.refl (G.matching i) := by
  have hN := exchangeMatching_perfect (G.perfect i) rep hrep q hsupported
  obtain ⟨j, hj⟩ := G.complete (exchangeMatching rep q) hN
  obtain ⟨e, he⟩ := hfixed
  have hshared : e.1 ∈ G.matching j := by
    rw [← hj, ← exchangeEdge_of_fixed rep hrep q e he]
    exact Finset.mem_image.mpr ⟨e, Finset.mem_univ _, rfl⟩
  have hij : i = j := G.eq_of_shared_edge e.2 hshared
  apply exchangeMatching_eq_implies_eq_refl (G.perfect i) rep hrep hsize q
  simpa only [hij] using hj

/-- The loopless replacement digraph on the matching edges. -/
def exchangeArc (H : Hypergraph V) (rep : M → V) (e f : M) : Prop :=
  e ≠ f ∧ insert (rep f) (e.1.erase (rep e)) ∈ H

instance (H : Hypergraph V) (rep : M → V) : DecidableRel (exchangeArc H rep) :=
  fun e f => inferInstanceAs (Decidable (e ≠ f ∧ insert (rep f) (e.1.erase (rep e)) ∈ H))

/-- Every supported nonidentity partial cycle would violate this property. -/
def NoPartialPermutations {W : Type*} (R : W → W → Prop) : Prop :=
  ∀ q : Equiv.Perm W, (∀ w, q w = w ∨ R w (q w)) →
    (∃ w, q w = w) → q = Equiv.refl W

/-- The exchange digraph of a rigid hypergraph has no proper supported cycle. -/
theorem rigid_exchange_noPartialPermutations (G : RigidFamily H I) (i : I)
    (rep : G.matching i → V) (hrep : ∀ e, rep e ∈ e.1)
    (hsize : ∀ e : G.matching i, 2 ≤ e.1.card) :
    NoPartialPermutations (exchangeArc H rep) := by
  intro q hq hfixed
  apply rigid_exchange_fixed_implies_identity G i rep hrep hsize q _ hfixed
  intro e
  rcases hq e with hfix | harc
  · rw [exchangeEdge_of_fixed rep hrep q e hfix]
    exact (G.perfect i).subset e.2
  · exact harc.2

end RigidGHZ.UpperBounds
