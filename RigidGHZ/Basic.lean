module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic

@[expose] public section

namespace RigidGHZ

/-- A finite simple hypergraph, represented by its finite set of edges. -/
abbrev Hypergraph (V : Type*) := Finset (Finset V)

variable {V : Type*} [DecidableEq V]

/-- Every edge has exactly `r` vertices. -/
def Uniform (H : Hypergraph V) (r : ℕ) : Prop :=
  ∀ e ∈ H, e.card = r

/-- A perfect matching consists of edges of `H` and covers each vertex exactly once. -/
def PerfectMatching (H M : Hypergraph V) : Prop :=
  M ⊆ H ∧ ∀ v : V, (M.filter (fun e => v ∈ e)).card = 1

/-- The number of edges containing a vertex. -/
def degree (H : Hypergraph V) (v : V) : ℕ :=
  (H.filter (fun e => v ∈ e)).card

/-- A specified, exhaustive decomposition into pairwise edge-disjoint perfect matchings. -/
structure RigidFamily (H : Hypergraph V) (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching
  complete : ∀ M, PerfectMatching H M → ∃ i, M = matching i

/-- `H` is `d`-rigid: its edges partition into `d` perfect matchings, and it has no others. -/
def IsRigid (H : Hypergraph V) (d : ℕ) : Prop :=
  Nonempty (RigidFamily H (Fin d))

namespace PerfectMatching

 theorem subset {H M : Hypergraph V} (h : PerfectMatching H M) : M ⊆ H := h.1

 theorem existsUnique_edge {H M : Hypergraph V} (h : PerfectMatching H M) (v : V) :
    ∃! e, e ∈ M ∧ v ∈ e := by
  obtain ⟨e, he⟩ := Finset.card_eq_one.mp (h.2 v)
  have hem : e ∈ M.filter (fun e => v ∈ e) := by rw [he]; simp
  refine ⟨e, Finset.mem_filter.mp hem, ?_⟩
  intro f hf
  have hfm : f ∈ M.filter (fun e => v ∈ e) := Finset.mem_filter.mpr hf
  rw [he] at hfm
  exact Finset.mem_singleton.mp hfm

 theorem of_existsUnique {H M : Hypergraph V} (hsub : M ⊆ H)
    (h : ∀ v : V, ∃! e, e ∈ M ∧ v ∈ e) : PerfectMatching H M := by
  refine ⟨hsub, fun v => ?_⟩
  obtain ⟨e, he, hu⟩ := h v
  apply Finset.card_eq_one.mpr
  refine ⟨e, ?_⟩
  ext f
  simp only [Finset.mem_filter, Finset.mem_singleton]
  constructor
  · exact hu f
  · rintro rfl
    exact he

 theorem mono {H H' M : Hypergraph V} (h : PerfectMatching H M) (hHH' : H ⊆ H') :
    PerfectMatching H' M := ⟨Finset.Subset.trans h.1 hHH', h.2⟩

 theorem disjoint_edges {H M : Hypergraph V} (h : PerfectMatching H M)
    {e f : Finset V} (he : e ∈ M) (hf : f ∈ M) (hne : e ≠ f) : Disjoint e f := by
  apply Finset.disjoint_left.mpr
  intro v hve hvf
  obtain ⟨g, hg, hu⟩ := h.existsUnique_edge v
  exact hne ((hu e ⟨he, hve⟩).trans (hu f ⟨hf, hvf⟩).symm)

 theorem nonempty [Nonempty V] {H M : Hypergraph V} (h : PerfectMatching H M) :
    M.Nonempty := by
  obtain ⟨v⟩ := ‹Nonempty V›
  obtain ⟨e, he, _⟩ := h.existsUnique_edge v
  exact ⟨e, he.1⟩

 theorem biUnion_eq_univ [Fintype V] {H M : Hypergraph V} (h : PerfectMatching H M) :
    M.biUnion id = Finset.univ := by
  ext v
  simp only [Finset.mem_biUnion, id_eq, Finset.mem_univ, iff_true]
  obtain ⟨e, he, _⟩ := h.existsUnique_edge v
  exact ⟨e, he.1, he.2⟩

 theorem card_mul_eq [Fintype V] {H M : Hypergraph V} {r : ℕ}
    (hH : Uniform H r) (hM : PerfectMatching H M) :
    M.card * r = Fintype.card V := by
  have hdis : (M : Set (Finset V)).PairwiseDisjoint id := by
    intro e he f hf hne
    exact hM.disjoint_edges he hf hne
  have hc := Finset.card_biUnion hdis
  rw [hM.biUnion_eq_univ] at hc
  simp only [Finset.card_univ, id_eq] at hc
  rw [hc]
  symm
  calc
    ∑ e ∈ M, e.card = ∑ _e ∈ M, r := by
      apply Finset.sum_congr rfl
      intro e he
      exact hH e (hM.subset he)
    _ = M.card * r := by simp

 theorem eq_of_subset {H M N : Hypergraph V} (hM : PerfectMatching H M)
    (hN : PerfectMatching H N) (hsub : M ⊆ N)
    (hnonempty : ∀ e ∈ N, e.Nonempty) : M = N := by
  apply Finset.Subset.antisymm hsub
  intro e he
  obtain ⟨v, hv⟩ := hnonempty e he
  obtain ⟨f, hf, hu⟩ := hM.existsUnique_edge v
  obtain ⟨g, hg, hgu⟩ := hN.existsUnique_edge v
  have hef : e = f := (hgu e ⟨he, hv⟩).trans (hgu f ⟨hsub hf.1, hf.2⟩).symm
  simpa only [hef] using hf.1

end PerfectMatching

namespace RigidFamily

variable {H : Hypergraph V} {I : Type*} [Fintype I]

 theorem mem_iff (F : RigidFamily H I) {e : Finset V} :
    e ∈ H ↔ ∃ i, e ∈ F.matching i := by
  calc
    e ∈ H ↔ e ∈ Finset.univ.biUnion F.matching :=
      iff_of_eq (congrArg (fun K : Hypergraph V => e ∈ K) F.covers)
    _ ↔ ∃ i, e ∈ F.matching i := by simp

 theorem matching_injective [Nonempty V] (F : RigidFamily H I) :
    Function.Injective F.matching := by
  intro i j hij
  by_contra hne
  obtain ⟨e, he⟩ := (F.perfect i).nonempty
  have hj : e ∈ F.matching j := by rwa [← hij]
  exact Finset.disjoint_left.mp (F.edge_disjoint hne) he hj

 theorem eq_of_shared_edge (F : RigidFamily H I) {i j : I} {e : Finset V}
    (hi : e ∈ F.matching i) (hj : e ∈ F.matching j) : i = j := by
  by_contra hne
  exact Finset.disjoint_left.mp (F.edge_disjoint hne) hi hj

/-- Reindex a rigid family by an equivalence of its labels. -/
def reindex {J : Type*} [Fintype J] (F : RigidFamily H I) (e : J ≃ I) :
    RigidFamily H J where
  matching := fun j => F.matching (e j)
  perfect := fun j => F.perfect (e j)
  edge_disjoint := by
    intro i j hij
    exact F.edge_disjoint (fun h => hij (e.injective h))
  covers := by
    ext x
    rw [F.mem_iff]
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨e.symm i, by simpa using hi⟩
    · rintro ⟨j, hj⟩
      exact ⟨e j, hj⟩
  complete := by
    intro M hM
    obtain ⟨i, hi⟩ := F.complete M hM
    exact ⟨e.symm i, by simpa using hi⟩

/-- Keep any chosen set of the prescribed matching classes. -/
def restrict [DecidableEq I] [Nonempty V] (F : RigidFamily H I) (s : Finset I) :
    RigidFamily (s.biUnion F.matching) s where
  matching := fun i => F.matching i.1
  perfect := by
    intro i
    refine ⟨?_, (F.perfect i.1).2⟩
    intro e he
    exact Finset.mem_biUnion.mpr ⟨i.1, i.2, he⟩
  edge_disjoint := by
    intro i j hij
    exact F.edge_disjoint (fun h => hij (Subtype.ext h))
  covers := by
    ext e
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, hi, he⟩
      exact ⟨⟨i, hi⟩, he⟩
    · rintro ⟨i, he⟩
      exact ⟨i.1, i.2, he⟩
  complete := by
    intro M hM
    have hsub : s.biUnion F.matching ⊆ H := by
      intro e he
      obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
      exact (F.perfect i).subset hei
    obtain ⟨i, hi⟩ := F.complete M (hM.mono hsub)
    obtain ⟨e, he⟩ := hM.nonempty
    obtain ⟨j, hj, hej⟩ := Finset.mem_biUnion.mp (hM.subset he)
    have hei : e ∈ F.matching i := by simpa only [← hi] using he
    have hij : i = j := F.eq_of_shared_edge hei hej
    subst j
    exact ⟨⟨i, hj⟩, hi⟩

 theorem regular (F : RigidFamily H I) (v : V) : degree H v = Fintype.card I := by
  classical
  have hset : H.filter (fun e => v ∈ e) =
      Finset.univ.biUnion (fun i => (F.matching i).filter (fun e => v ∈ e)) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and]
    rw [F.mem_iff]
    aesop
  have hdis : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint
      (fun i => (F.matching i).filter (fun e => v ∈ e)) := by
    intro i hi j hj hij
    exact (F.edge_disjoint hij).mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold degree
  rw [hset, Finset.card_biUnion hdis]
  simp only [(F.perfect _).2 v]
  simp

 theorem card_edges [Fintype V] (F : RigidFamily H I) {r m : ℕ}
    (hH : Uniform H r) (hr : 0 < r) (hV : Fintype.card V = r * m) :
    H.card = Fintype.card I * m := by
  classical
  have hm : ∀ i, (F.matching i).card = m := by
    intro i
    have heq := (F.perfect i).card_mul_eq hH
    rw [hV, Nat.mul_comm r m] at heq
    exact Nat.eq_of_mul_eq_mul_right hr heq
  have hdis : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint F.matching := by
    intro i hi j hj hij
    exact F.edge_disjoint hij
  have hc : (Finset.univ.biUnion F.matching).card = Fintype.card I * m := by
    rw [Finset.card_biUnion hdis]
    simp [hm]
  exact (congrArg Finset.card F.covers).trans hc

end RigidFamily

end RigidGHZ
