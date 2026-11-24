module

public import RigidGHZ.Basic

/-!
# Labels of accepted emission patterns

The purely combinatorial part of Proposition 2.1. Each source edge has the
label of its prescribed matching class. At every vertex a label identifies
the unique incident source of that class. Consequently different perfect
matchings yield different label strings; no cancellation between different
matching amplitudes is possible in this model.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

variable {V I : Type*} [DecidableEq V] [Fintype I]

/-- A prescribed edge decomposition, without assuming that it is exhaustive on matchings. -/
structure MatchingDecomposition (H : Hypergraph V) (I : Type*) [Fintype I] where
  matching : I → Hypergraph V
  perfect : ∀ i, PerfectMatching H (matching i)
  edge_disjoint : Pairwise (fun i j => Disjoint (matching i) (matching j))
  covers : H = Finset.univ.biUnion matching

/-- The actual perfect matchings of `H`, not just the prescribed ones. -/
def PerfectMatchings (H : Hypergraph V) := {M : Hypergraph V // PerfectMatching H M}

variable {H : Hypergraph V}

def incidentEdge (M : PerfectMatchings H) (v : V) : Finset V :=
  Classical.choose (M.2.existsUnique_edge v)

theorem incidentEdge_spec (M : PerfectMatchings H) (v : V) :
    incidentEdge M v ∈ M.1 ∧ v ∈ incidentEdge M v :=
  (Classical.choose_spec (M.2.existsUnique_edge v)).1

theorem incidentEdge_eq (M : PerfectMatchings H) {v : V} {e : Finset V}
    (he : e ∈ M.1) (hv : v ∈ e) : incidentEdge M v = e :=
  ((Classical.choose_spec (M.2.existsUnique_edge v)).2 e ⟨he, hv⟩).symm

namespace MatchingDecomposition

variable (F : MatchingDecomposition H I)

theorem mem_iff {e : Finset V} : e ∈ H ↔ ∃ i, e ∈ F.matching i := by
  calc
    e ∈ H ↔ e ∈ Finset.univ.biUnion F.matching :=
      iff_of_eq (congrArg (fun K : Hypergraph V => e ∈ K) F.covers)
    _ ↔ ∃ i, e ∈ F.matching i := by simp

def edgeColor (e : H) : I := Classical.choose (F.mem_iff.mp e.2)

theorem edgeColor_mem (e : H) : e.1 ∈ F.matching (F.edgeColor e) :=
  Classical.choose_spec (F.mem_iff.mp e.2)

theorem edgeColor_eq_of_mem (e : H) {i : I} (he : e.1 ∈ F.matching i) :
    F.edgeColor e = i := by
  by_contra h
  exact Finset.disjoint_left.mp (F.edge_disjoint h) (F.edgeColor_mem e) he

/-- The observed source-label string of a perfect matching. -/
def labelString (M : PerfectMatchings H) (v : V) : I :=
  F.edgeColor ⟨incidentEdge M v, M.2.subset (incidentEdge_spec M v).1⟩

theorem edge_mem_labelClass (M : PerfectMatchings H) {v : V} {e : Finset V}
    (he : e ∈ M.1) (hv : v ∈ e) : e ∈ F.matching (F.labelString M v) := by
  have h : incidentEdge M v ∈ F.matching (F.labelString M v) :=
    F.edgeColor_mem ⟨incidentEdge M v, M.2.subset (incidentEdge_spec M v).1⟩
  rwa [incidentEdge_eq M he hv] at h

theorem labelString_eq_of_mem (M : PerfectMatchings H) {v : V} {e : Finset V}
    (he : e ∈ M.1) (hv : v ∈ e) {i : I} (hi : e ∈ F.matching i) :
    F.labelString M v = i := by
  apply F.edgeColor_eq_of_mem
  simpa only [incidentEdge_eq M he hv] using hi

/-- The prescribed class is itself an actual perfect matching. -/
def prescribed (i : I) : PerfectMatchings H := ⟨F.matching i, F.perfect i⟩

theorem labelString_prescribed (i : I) :
    F.labelString (F.prescribed i) = fun _ => i := by
  funext v
  have h := incidentEdge_spec (F.prescribed i) v
  exact F.labelString_eq_of_mem (F.prescribed i) h.1 h.2 h.1

/-- A label string determines its perfect matching when source supports are nonempty. -/
theorem labelString_injective (hnonempty : ∀ e ∈ H, e.Nonempty) :
    Function.Injective F.labelString := by
  intro M N hlabels
  apply Subtype.ext
  apply M.2.eq_of_subset N.2
  · intro e he
    obtain ⟨v, hv⟩ := hnonempty e (M.2.subset he)
    let f := incidentEdge N v
    have hf : f ∈ N.1 ∧ v ∈ f := incidentEdge_spec N v
    have heclass := F.edge_mem_labelClass M he hv
    have hfclass := F.edge_mem_labelClass N hf.1 hf.2
    rw [← congrFun hlabels v] at hfclass
    obtain ⟨g, hg, hu⟩ := (F.perfect (F.labelString M v)).existsUnique_edge v
    have hef : e = f := (hu e ⟨heclass, hv⟩).trans (hu f ⟨hfclass, hf.2⟩).symm
    simpa only [hef] using hf.1
  · intro e he
    exact hnonempty e (N.2.subset he)

theorem labelString_eq_const_iff (hnonempty : ∀ e ∈ H, e.Nonempty)
    (M : PerfectMatchings H) (i : I) :
    F.labelString M = (fun _ => i) ↔ M.1 = F.matching i := by
  constructor
  · intro h
    have heq : F.labelString M = F.labelString (F.prescribed i) := by
      rw [F.labelString_prescribed]
      exact h
    exact congrArg Subtype.val (F.labelString_injective hnonempty heq)
  · intro h
    have heq : M = F.prescribed i := Subtype.ext h
    rw [heq, F.labelString_prescribed]

/-- All label strings occurring as accepted emission patterns. -/
def acceptedLabels : Set (V → I) := Set.range F.labelString

/-- The GHZ basis strings, one constant string for each prescribed class. -/
def constantLabels (_F : MatchingDecomposition H I) : Set (V → I) :=
  Set.range (fun i : I => fun _ : V => i)

theorem constantLabels_subset : F.constantLabels ⊆ F.acceptedLabels := by
  rintro s ⟨i, rfl⟩
  exact ⟨F.prescribed i, F.labelString_prescribed i⟩

/-- Exact label support is equivalent to completeness of the prescribed matching list. -/
theorem acceptedLabels_eq_iff (hnonempty : ∀ e ∈ H, e.Nonempty) :
    F.acceptedLabels = F.constantLabels ↔
      ∀ M, PerfectMatching H M → ∃ i, M = F.matching i := by
  constructor
  · intro h M hM
    have hm : F.labelString ⟨M, hM⟩ ∈ F.acceptedLabels := ⟨⟨M, hM⟩, rfl⟩
    rw [h] at hm
    obtain ⟨i, hi⟩ := hm
    exact ⟨i, (F.labelString_eq_const_iff hnonempty ⟨M, hM⟩ i).mp hi.symm⟩
  · intro hc
    apply Set.Subset.antisymm ?_ F.constantLabels_subset
    rintro s ⟨M, rfl⟩
    obtain ⟨i, hi⟩ := hc M.1 M.2
    exact ⟨i, ((F.labelString_eq_const_iff hnonempty M i).mpr hi).symm⟩

/-- Complete the given decomposition to a rigid-family certificate. -/
def toRigidFamily (hcomplete : ∀ M, PerfectMatching H M → ∃ i, M = F.matching i) :
    RigidFamily H I where
  matching := F.matching
  perfect := F.perfect
  edge_disjoint := F.edge_disjoint
  covers := F.covers
  complete := hcomplete

/-- Any rigid decomposition of the same nonempty vertex set forces this one to be complete. -/
theorem complete_of_rigidFamily [Nonempty V] {J : Type*} [Fintype J]
    (G : RigidFamily H J) :
    ∀ M, PerfectMatching H M → ∃ i, M = F.matching i := by
  intro M hM
  obtain ⟨j, hj⟩ := G.complete M hM
  obtain ⟨e, he⟩ := hM.nonempty
  obtain ⟨i, hei⟩ := F.mem_iff.mp (hM.subset he)
  obtain ⟨j', hj'⟩ := G.complete (F.matching i) (F.perfect i)
  have hej : e ∈ G.matching j := by simpa only [← hj] using he
  have hej' : e ∈ G.matching j' := by simpa only [← hj'] using hei
  have hji : j = j' := G.eq_of_shared_edge hej hej'
  exact ⟨i, hj.trans (hji ▸ hj'.symm)⟩

end MatchingDecomposition

/-- Proposition 2.1 at the combinatorial support level. -/
theorem acceptedLabels_eq_constantLabels_iff_isRigid [Nonempty V] {d : ℕ}
    (F : MatchingDecomposition H (Fin d))
    (hnonempty : ∀ e ∈ H, e.Nonempty) :
    F.acceptedLabels = F.constantLabels ↔ IsRigid H d := by
  rw [F.acceptedLabels_eq_iff hnonempty]
  constructor
  · intro h
    exact ⟨F.toRigidFamily h⟩
  · rintro ⟨G⟩
    exact F.complete_of_rigidFamily G

end RigidGHZ.SourceModel
