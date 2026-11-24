module

public import RigidGHZ.Supplement.LinearLift
public import RigidGHZ.Supplement.MarkedBinary
public import RigidGHZ.Supplement.Linearity
public import RigidGHZ.Supplement.BoundedHelpers

/-! Construction interfaces for the genuine linear seeds in Supplement S7.
Every interface returns ordinary rigid hypergraphs and the standard pair bound. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement

/-- A canonical balanced linear seed with precisely `d` prescribed matchings. -/
abbrev LinearSeed (q d : ℕ) : Prop := BoundedRigid 3 q d (pairBounds d 1)

 theorem LinearSeed.restrict {q d t : ℕ} (h : LinearSeed q d) (ht : t ≤ d) (hq : 1 ≤ q) :
    LinearSeed q t := h.restrict_pair ht (by decide) hq

 theorem LinearSeed.realize {q d : ℕ} (h : LinearSeed q d) :
    ∃ H : Hypergraph (Fin 3 × Fin q), Uniform H 3 ∧ BalancedPartite H 3 q ∧
      IsRigid H d ∧ IsLinear H := by
  obtain ⟨H, hU, hP, hR, hD⟩ := h
  refine ⟨H, hU, hP, hR, (linear_iff_pair_bound H).mpr ?_⟩
  simpa [pairBounds] using hD 2 (by decide)

namespace Affine

variable {m L : ℕ} [NeZero m] [NeZero L]

/-- A marking with a specified three-bit encoding, used for monotone codes. -/
def Marking.ofTripleEmbedding {S : Finset (ZMod m)} (hm : 4 ≤ m) (e : S ↪ Fin 8) : Marking S := {
  marked := threeMarks hm
  sum_lt := by rw [threeMarks_sum]; omega
  superincreasing := threeMarks_superincreasing hm
  code := tripleCode e
  outside := tripleCode_outside hm e
  injective := tripleCode_injective hm e }

 theorem Marking.ofTripleEmbedding_mono {S : Finset (ZMod m)} (hm : 4 ≤ m) (e : S ↪ Fin 8)
    (δ : ZMod m)
    (hc : ∀ s t : S, t.val = s.val + δ → ∀ k : Fin 3,
      bit (binaryTriple (e t) k) ≤ bit (binaryTriple (e s) k)) :
    ∀ s t : S, t.val = s.val + δ → ∀ a,
      bit ((Marking.ofTripleEmbedding hm e).code t a) ≤
        bit ((Marking.ofTripleEmbedding hm e).code s a) := by
  intro s t hst a
  by_cases ha : a.val < 3
  · simpa [Marking.ofTripleEmbedding, tripleCode, ha] using hc s t hst ⟨a.val, ha⟩
  · simp [Marking.ofTripleEmbedding, tripleCode, ha]

 theorem bank_large {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hm : 4 ≤ m) (hodd : Odd m) (hcop : m.Coprime L) (hS : S.card ≤ 8) (hL : 4 ≤ L) :
    LinearSeed (m * L) (2 * S.card) := by
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_large (by omega) hodd hcop (1 : ZMod m)
    isUnit_one (Marking.binary hm hS) hL
  exact boundedRigid_of_pair_bound hU hP hR hD

 theorem bank_two {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hm : 4 ≤ m) (hodd : Odd m) (hS : S.card ≤ 8) (δ : ZMod m) (hδ : IsUnit δ) :
    LinearSeed (m * 2) (2 * S.card - (shiftOverlap S δ).card) := by
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_two (by omega) hodd δ hδ (Marking.binary hm hS)
  exact boundedRigid_of_pair_bound hU hP hR hD

 theorem bank_three {lam : ZMod m} {S : Finset (ZMod m)} (B : Seed lam S)
    (hm : 4 ≤ m) (hodd : Odd m) (hcop : m.Coprime 3) (e : S ↪ Fin 8)
    (hc : ∀ s t : S, t.val = s.val + 1 → ∀ k : Fin 3,
      bit (binaryTriple (e t) k) ≤ bit (binaryTriple (e s) k)) :
    LinearSeed (m * 3) (2 * S.card) := by
  let C := Marking.ofTripleEmbedding hm e
  obtain ⟨H, hH, hU, hP, hR, hD⟩ := B.linear_three (by omega) hodd hcop (1 : ZMod m)
    isUnit_one C (Marking.ofTripleEmbedding_mono hm e 1 hc)
  exact boundedRigid_of_pair_bound hU hP hR hD

end Affine
end RigidGHZ.Supplement
