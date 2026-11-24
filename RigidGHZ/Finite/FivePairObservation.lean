module

public import RigidGHZ.Finite.FivePairSemantics
public import RigidGHZ.Finite.FivePairCertificates

/-! Appendix B, Claim B.1, for arbitrary selected subsets of the two copies
of the two-element subsets of a five-element ground set. -/

@[expose] public section

namespace RigidGHZ.Finite.FivePair

theorem five_edges_exact {L R : Finset Pair} (h : Conditions L R)
    (hcount : (edges L R).card = 5) : L.card + R.card = 10 := by
  obtain ⟨f, hL, hR⟩ := extract_five h hcount
  have hcross : CrossFree id f := family_crossFree h Function.injective_id hL hR
  obtain ⟨hl, hr⟩ := five_certificate f hcross
  exact five_conclusion h hL hR hl hr

theorem four_edges_bound {L R : Finset Pair} (h : Conditions L R)
    (hcount : (edges L R).card = 4) : L.card + R.card ≤ 9 := by
  obtain ⟨c, f, hL, hR⟩ := extract_four h hcount
  have hcross : CrossFree c.succAbove f :=
    family_crossFree h (Fin.succAbove_right_injective (p := c)) hL hR
  obtain ⟨hl, hr, ha⟩ := four_certificate c f hcross
  exact four_conclusion h hcount hL hR hl hr ha

/-- Both conclusions of the standalone five-pair observation. The finite
certificates are preceded by a proof recovering their indexed input from
the entire induced subgraph on the selected vertices. -/
theorem observation {L R : Finset Pair} (h : Conditions L R) :
    ((edges L R).card = 5 → L.card + R.card = 10) ∧
    ((edges L R).card = 4 → L.card + R.card ≤ 9) :=
  ⟨five_edges_exact h, four_edges_bound h⟩

end RigidGHZ.Finite.FivePair
