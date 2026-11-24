module

public import RigidGHZ.Finite.ComplementaryExtrema

/-! Removing edges that occur in no perfect matching.  This proves the
equivalence of the two extremal formulations in the paper's definitions. -/

@[expose] public section

noncomputable section

namespace RigidGHZ

variable {V : Type*} [Fintype V] [DecidableEq V]

def matchingCore (H : Hypergraph V) : Hypergraph V :=
  (Finite.allPerfectMatchings H).biUnion id

theorem mem_matchingCore {H : Hypergraph V} {e : Finset V} :
    e ∈ matchingCore H ↔ ∃ M, PerfectMatching H M ∧ e ∈ M := by
  simp only [matchingCore, Finset.mem_biUnion, Finite.mem_allPerfectMatchings, id_eq]

theorem matchingCore_subset (H : Hypergraph V) : matchingCore H ⊆ H := by
  intro e he
  obtain ⟨M, hM, heM⟩ := mem_matchingCore.mp he
  exact hM.subset heM

theorem perfectMatching_core_iff {H M : Hypergraph V} :
    PerfectMatching (matchingCore H) M ↔ PerfectMatching H M := by
  constructor
  · exact fun h => h.mono (matchingCore_subset H)
  · intro h
    exact ⟨fun e he => mem_matchingCore.mpr ⟨M, h, he⟩, h.2⟩

theorem matchingCore_uniform {H : Hypergraph V} {r : ℕ} (hU : Uniform H r) :
    Uniform (matchingCore H) r := fun e he => hU e (matchingCore_subset H he)

theorem matchingCore_balanced {H : Hypergraph V} {r m : ℕ}
    (hP : BalancedPartite H r m) : BalancedPartite (matchingCore H) r m := by
  obtain ⟨c, hc, he⟩ := hP
  exact ⟨c, hc, fun e hecore i => he e (matchingCore_subset H hecore) i⟩

def PairwiseDisjointPerfectMatchings (H : Hypergraph V) : Prop :=
  ∀ M N, PerfectMatching H M → PerfectMatching H N → M ≠ N → Disjoint M N

def matchingCoreFamily (H : Hypergraph V) (hd : PairwiseDisjointPerfectMatchings H) :
    RigidFamily (matchingCore H) (Finite.allPerfectMatchings H) where
  matching := Subtype.val
  perfect := fun i => perfectMatching_core_iff.mpr (Finite.mem_allPerfectMatchings.mp i.property)
  edge_disjoint := by
    intro i j hij
    exact hd i.val j.val (Finite.mem_allPerfectMatchings.mp i.property)
      (Finite.mem_allPerfectMatchings.mp j.property) (fun h => hij (Subtype.ext h))
  covers := by
    ext e
    simp only [matchingCore, Finset.mem_biUnion, Finset.mem_univ, true_and, id_eq]
    exact ⟨fun ⟨M, hM, he⟩ => ⟨⟨M, hM⟩, he⟩,
      fun ⟨M, he⟩ => ⟨M.val, M.property, he⟩⟩
  complete := fun M hM =>
    ⟨⟨M, Finite.mem_allPerfectMatchings.mpr (perfectMatching_core_iff.mp hM)⟩, rfl⟩

theorem matchingCore_rigid (H : Hypergraph V) (hd : PairwiseDisjointPerfectMatchings H) :
    IsRigid (matchingCore H) (Finite.allPerfectMatchings H).card := by
  let R := matchingCoreFamily H hd
  let e := Fintype.equivFin (Finite.allPerfectMatchings H)
  simpa only [Fintype.card_coe] using
    (show IsRigid (matchingCore H) (Fintype.card (Finite.allPerfectMatchings H)) from
      ⟨R.reindex e.symm⟩)

theorem IsRigid.pairwiseDisjointPerfectMatchings {H : Hypergraph V} {d : ℕ}
    (hR : IsRigid H d) : PairwiseDisjointPerfectMatchings H := by
  obtain ⟨R⟩ := hR
  intro M N hM hN hne
  obtain ⟨i, rfl⟩ := R.complete M hM
  obtain ⟨j, rfl⟩ := R.complete N hN
  exact R.edge_disjoint (fun h => hne (congrArg R.matching h))

/-- Dead-edge deletion preserves every perfect matching and produces an
ordinary rigid hypergraph with exactly the original number of matchings. -/
theorem prune_dead_edges (H : Hypergraph V) (hd : PairwiseDisjointPerfectMatchings H) :
    ∃ K : Hypergraph V, K ⊆ H ∧
      (∀ M, PerfectMatching K M ↔ PerfectMatching H M) ∧
      IsRigid K (Finite.allPerfectMatchings H).card :=
  ⟨matchingCore H, matchingCore_subset H, fun _ => perfectMatching_core_iff,
    matchingCore_rigid H hd⟩

end RigidGHZ
