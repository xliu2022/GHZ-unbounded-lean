module

public import RigidGHZ.Supplement.Periodic.Enumeration

/-! The finite candidate-size bound used by the periodic search certificate. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  (D : Scheme V E)

 theorem local_configuration_size_bound {r : ℕ} (hr : 0 < r)
    (hU : ∀ e, (D.edge e).card = r) {A : Finset E} (hA : D.LocalConfig A) :
    A.card ≤ (Fintype.card V + D.allOutgoing.card) / r := by
  have hl : (D.localVertices A).card = ∑ e ∈ A, (D.localPart e).card := by
    exact Finset.card_biUnion (fun e he f hf hef => hA.1 e he f hf hef)
  have ho : (D.output A).card = ∑ e ∈ A, (D.outgoing e).card := by
    exact Finset.card_biUnion (fun e he f hf hef => hA.2.1 e he f hf hef)
  have hsum : (D.localVertices A).card + (D.output A).card = A.card * r := by
    rw [hl, ho, ← Finset.sum_add_distrib]
    have heq : ∀ e, (D.localPart e).card + (D.outgoing e).card = r := by
      intro e
      exact (Finset.card_sdiff_add_card_eq_card (D.outgoing_subset e)).trans (hU e)
    simp only [heq, Finset.sum_const, smul_eq_mul]
  have hlocal : (D.localVertices A).card ≤ Fintype.card V := Finset.card_le_univ _
  have houtput : (D.output A).card ≤ D.allOutgoing.card := Finset.card_le_card (by
    intro v hv
    obtain ⟨e, he, hve⟩ := Finset.mem_biUnion.mp hv
    exact Finset.mem_biUnion.mpr ⟨e, Finset.mem_univ _, hve⟩)
  apply (Nat.le_div_iff_mul_le hr).mpr
  omega

end RigidGHZ.Supplement.Periodic.Scheme
