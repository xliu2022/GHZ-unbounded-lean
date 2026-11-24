module

public import RigidGHZ.Supplement.GraftData

/-! Fibers of partial matchings in transversal hypergraphs. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement

variable {A W : Type*} [Fintype A] [Fintype W] [DecidableEq A] [DecidableEq W]

def edgeFiber (e : Finset (A × W)) (a : A) : Finset W :=
  (e.filter (fun v => v.1 = a)).image Prod.snd

@[simp] theorem mem_edgeFiber (e : Finset (A × W)) (a : A) (w : W) :
    w ∈ edgeFiber e a ↔ (a, w) ∈ e := by
  simp only [edgeFiber, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨⟨b, u⟩, ⟨h, hba⟩, huw⟩
    dsimp at hba huw
    simpa only [hba, huw] using h
  · intro h
    exact ⟨(a, w), ⟨h, rfl⟩, rfl⟩

@[simp] theorem edgeFiber_tuple (x : A → W) (a : A) : edgeFiber (tupleEdge x) a = {x a} := by
  ext w
  simp

 def matchingFiber (Q : Hypergraph (A × W)) (a : A) : Finset W :=
  Q.biUnion (fun e => edgeFiber e a)

@[simp] theorem mem_matchingFiber (Q : Hypergraph (A × W)) (a : A) (w : W) :
    w ∈ matchingFiber Q a ↔ ∃ e ∈ Q, (a, w) ∈ e := by
  simp [matchingFiber]

 theorem matchingFiber_card (Q : Hypergraph (A × W))
    (htrans : ∀ e ∈ Q, ∃ x : A → W, e = tupleEdge x)
    (hdis : ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint e f) (a : A) :
    (matchingFiber Q a).card = Q.card := by
  have hd : (Q : Set (Finset (A × W))).PairwiseDisjoint (fun e => edgeFiber e a) := by
    intro e he f hf hef
    apply Finset.disjoint_left.mpr
    intro w hwe hwf
    exact Finset.disjoint_left.mp (hdis e he f hf hef)
      ((mem_edgeFiber e a w).mp hwe) ((mem_edgeFiber f a w).mp hwf)
  rw [matchingFiber, Finset.card_biUnion hd]
  calc
    ∑ e ∈ Q, (edgeFiber e a).card = ∑ _e ∈ Q, 1 := by
      apply Finset.sum_congr rfl
      intro e he
      obtain ⟨x, rfl⟩ := htrans e he
      simp
    _ = Q.card := by simp

/-- Completing a partial transversal matching whose fibers omit exactly the
vertices of one edge gives a perfect matching. -/
theorem perfectMatching_insert_of_fibers {S Q : Hypergraph (A × W)} (z : A → W)
    (hQ : Q ⊆ S) (hz : tupleEdge z ∈ S)
    (hdis : ∀ e ∈ Q, ∀ f ∈ Q, e ≠ f → Disjoint e f)
    (hfib : ∀ a, matchingFiber Q a = Finset.univ.erase (z a)) :
    PerfectMatching S (insert (tupleEdge z) Q) := by
  apply PerfectMatching.of_existsUnique (Finset.insert_subset_iff.mpr ⟨hz, hQ⟩)
  rintro ⟨a, w⟩
  by_cases hw : w = z a
  · refine ⟨tupleEdge z, ⟨Finset.mem_insert_self _ _, mem_tupleEdge.mpr hw⟩, ?_⟩
    intro e he
    rcases Finset.mem_insert.mp he.1 with h | h
    · exact h
    · have hmem : w ∈ matchingFiber Q a := (mem_matchingFiber Q a w).mpr ⟨e, h, he.2⟩
      rw [hfib a] at hmem
      exact ((Finset.mem_erase.mp hmem).1 hw).elim
  · have hmem : w ∈ matchingFiber Q a := by rw [hfib a]; simp [hw]
    obtain ⟨e, heQ, hew⟩ := (mem_matchingFiber Q a w).mp hmem
    refine ⟨e, ⟨Finset.mem_insert_of_mem heQ, hew⟩, ?_⟩
    intro f hf
    rcases Finset.mem_insert.mp hf.1 with h | h
    · subst f
      exact (hw (mem_tupleEdge.mp hf.2)).elim
    · by_contra hne
      exact Finset.disjoint_left.mp (hdis f h e heQ hne) hf.2 hew

end RigidGHZ.Supplement
