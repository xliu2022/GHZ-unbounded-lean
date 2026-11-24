module

public import RigidGHZ.Finite.NineNormalized4a
public import RigidGHZ.Finite.NineNormalized4b
public import RigidGHZ.Finite.MatchingNormalization
public import RigidGHZ.Finite.NormalizationTransport

@[expose] public section
namespace RigidGHZ.Finite

/-- Reduce the normalized codegree-4 case by the verified matching symmetry. -/
theorem no_fourteen_normalized_4 (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 4)
    (hmax : ∀ a b : Fin 9, a ≠ b → (pairCompletions H a b).card ≤ 4) : False := by
  have h012 : ({0, 1, 2} : Finset (Fin 9)) ∈ H :=
    (hnorm 2 (by decide) (by decide)).mpr (by decide)
  obtain ⟨i, hi⟩ := F.mem_iff.mp h012
  obtain ⟨g, hg0, hg1, hg2, hgX, hgM⟩ := normalize_matching4 hU (F.perfect i) hi
  have hKnorm : NormalizedNinePair (relabelHypergraph g H) 4 :=
    normalized_pair_transport hnorm g hg0 hg1 hgX
  have hsub := ((F.perfect i).relabel g).subset
  have hKmax := pair_bound_relabel hmax g
  rcases hgM with ha | hb
  · apply no_fourteen_normalized_4a _ (hU.relabel g) (F.relabel g) hKnorm hKmax 
    · apply hsub
      rw [ha]
      simp
    · apply hsub
      rw [ha]
      simp
  · apply no_fourteen_normalized_4b _ (hU.relabel g) (F.relabel g) hKnorm hKmax 
    · apply hsub
      rw [hb]
      simp
    · apply hsub
      rw [hb]
      simp

end RigidGHZ.Finite
