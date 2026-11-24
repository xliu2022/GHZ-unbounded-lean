module

public import RigidGHZ.Finite.NineNormalized5a
public import RigidGHZ.Finite.NineNormalized5b
public import RigidGHZ.Finite.MatchingNormalization
public import RigidGHZ.Finite.NormalizationTransport

@[expose] public section
namespace RigidGHZ.Finite

/-- Reduce the normalized codegree-5 case by the verified matching symmetry. -/
theorem no_fourteen_normalized_5 (H : Hypergraph (Fin 9)) (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) (hnorm : NormalizedNinePair H 5) : False := by
  have h012 : ({0, 1, 2} : Finset (Fin 9)) ∈ H :=
    (hnorm 2 (by decide) (by decide)).mpr (by decide)
  obtain ⟨i, hi⟩ := F.mem_iff.mp h012
  obtain ⟨g, hg0, hg1, hg2, hgX, hgM⟩ := normalize_matching5 hU (F.perfect i) hi
  have hKnorm : NormalizedNinePair (relabelHypergraph g H) 5 :=
    normalized_pair_transport hnorm g hg0 hg1 hgX
  have hsub := ((F.perfect i).relabel g).subset
  rcases hgM with ha | hb
  · apply no_fourteen_normalized_5a _ (hU.relabel g) (F.relabel g) hKnorm 
    · apply hsub
      rw [ha]
      simp
    · apply hsub
      rw [ha]
      simp
  · apply no_fourteen_normalized_5b _ (hU.relabel g) (F.relabel g) hKnorm 
    · apply hsub
      rw [hb]
      simp
    · apply hsub
      rw [hb]
      simp

end RigidGHZ.Finite
