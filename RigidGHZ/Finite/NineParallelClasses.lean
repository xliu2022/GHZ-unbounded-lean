module

public import RigidGHZ.Finite.NineAlgebraicCounts

/-! The four parallel classes of the zero-sum class in the affine plane.

Every matching below is an ordinary finite set of actual affine lines.  The
finite checks concern only four directions and nine points; completeness uses
the already proved count of ordinary perfect matchings. -/

@[expose] public section

namespace RigidGHZ.Finite

local instance parallelPerfectDecidable (σ : AffinePlane) (M : Hypergraph AffinePlane) :
    Decidable (PerfectMatching (sumClass σ) M) := by
  unfold PerfectMatching
  infer_instance

/-- One representative for each of the four one-dimensional directions. -/
def affineDirection : Fin 4 → AffinePlane := ![(1, 0), (0, 1), (1, 1), (1, 2)]

/-- The set of cosets `{a + t b : t ∈ 𝔽₃}` of a fixed direction. -/
def affineParallelClass (b : AffinePlane) : Hypergraph AffinePlane :=
  Finset.univ.image (fun a : AffinePlane => affineLine a b)

def zeroParallelMatching (i : Fin 4) : Hypergraph AffinePlane :=
  affineParallelClass (affineDirection i)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem zeroParallelMatching_perfect (i : Fin 4) :
    PerfectMatching (sumClass 0) (zeroParallelMatching i) := by
  fin_cases i <;> decide +kernel

theorem zeroParallelMatching_injective : Function.Injective zeroParallelMatching := by
  decide +kernel

theorem zeroParallelMatching_edge_disjoint :
    Pairwise fun i j => Disjoint (zeroParallelMatching i) (zeroParallelMatching j) := by
  unfold Pairwise
  decide +kernel

theorem zeroParallelMatching_covers :
    sumClass 0 = Finset.univ.biUnion zeroParallelMatching := by
  decide +kernel

/-- Equality of actual finite sets of matchings, not merely equality of counts. -/
theorem sumClass_zero_matchings_eq_parallelClasses :
    sumClassMatchings 0 = Finset.univ.image zeroParallelMatching := by
  have hsub : Finset.univ.image zeroParallelMatching ⊆ sumClassMatchings 0 := by
    intro M hM
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hM
    exact (mem_sumClassMatchings 0 _).mpr (zeroParallelMatching_perfect i)
  have hleft : (sumClassMatchings 0).card = 4 := by
    simpa using sumClassMatchings_card (0 : AffinePlane)
  have hright : (Finset.univ.image zeroParallelMatching).card = 4 := by
    rw [Finset.card_image_of_injective _ zeroParallelMatching_injective]
    simp
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

/-- The four parallel classes are exactly the ordinary perfect matchings of
the twelve zero-sum triples. -/
theorem sumClass_zero_perfect_iff_parallel (M : Hypergraph AffinePlane) :
    PerfectMatching (sumClass 0) M ↔ ∃ i : Fin 4, M = zeroParallelMatching i := by
  rw [← mem_sumClassMatchings, sumClass_zero_matchings_eq_parallelClasses]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun _ => eq_comm

/-- The explicit parallel classes give the whole rigidity structure, including
their disjointness as edge sets and their union of all twelve lines. -/
def zeroParallelFamily : RigidFamily (sumClass 0) (Fin 4) where
  matching := zeroParallelMatching
  perfect := zeroParallelMatching_perfect
  edge_disjoint := zeroParallelMatching_edge_disjoint
  covers := zeroParallelMatching_covers
  complete := fun M hM => (sumClass_zero_perfect_iff_parallel M).mp hM

theorem sumClass_zero_rigid : IsRigid (sumClass 0) 4 := ⟨zeroParallelFamily⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
/-- For distinct lines written in the four canonical directions, disjointness
means precisely equality of directions. The distinctness premise excludes a
line being compared with itself. -/
theorem affineLine_disjoint_iff_parallel (i j : Fin 4) (a b : AffinePlane)
    (hne : affineLine a (affineDirection i) ≠ affineLine b (affineDirection j)) :
    Disjoint (affineLine a (affineDirection i)) (affineLine b (affineDirection j)) ↔
      i = j := by
  fin_cases i <;> fin_cases j <;> (revert a b; decide +kernel)

theorem affineParallelClass_card {σ : AffinePlane} (hσ : σ ≠ 0) :
    (affineParallelClass σ).card = 3 := by
  have h : ∀ σ : AffinePlane, σ ≠ 0 → (affineParallelClass σ).card = 3 := by
    decide +kernel
  exact h σ hσ

/-- The cosets of each nonzero direction partition the nine points. -/
theorem affineParallelClass_partition {σ : AffinePlane} (hσ : σ ≠ 0) :
    (∀ A ∈ affineParallelClass σ, ∀ B ∈ affineParallelClass σ,
      A ≠ B → Disjoint A B) ∧
      Finset.univ = (affineParallelClass σ).biUnion id := by
  have h : ∀ σ : AffinePlane, σ ≠ 0 →
      (∀ A ∈ affineParallelClass σ, ∀ B ∈ affineParallelClass σ,
        A ≠ B → Disjoint A B) ∧
        Finset.univ = (affineParallelClass σ).biUnion id := by
    decide +kernel
  exact h σ hσ

end RigidGHZ.Finite
