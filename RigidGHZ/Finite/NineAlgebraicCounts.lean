module

public import RigidGHZ.Finite.NineAlgebraic

/-! The per-sum-class counts in the algebraic nine-vertex construction. -/

@[expose] public section

namespace RigidGHZ.Finite

local instance sumClassPerfectDecidable (σ : AffinePlane) (M : Hypergraph AffinePlane) :
    Decidable (PerfectMatching (sumClass σ) M) := by
  unfold PerfectMatching
  infer_instance

theorem sumClass_uniform (σ : AffinePlane) : Uniform (sumClass σ) 3 := by
  intro e he
  exact (Finset.mem_powersetCard.mp (Finset.mem_filter.mp he).1).2

/-- A finite search domain containing precisely the ordinary perfect matchings
of one sum class; the size-three restriction is proved below. -/
def sumClassMatchings (σ : AffinePlane) : Finset (Hypergraph AffinePlane) :=
  ((sumClass σ).powersetCard 3).filter (PerfectMatching (sumClass σ))

theorem mem_sumClassMatchings (σ : AffinePlane) (M : Hypergraph AffinePlane) :
    M ∈ sumClassMatchings σ ↔ PerfectMatching (sumClass σ) M := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · intro h
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨h.1, ?_⟩, h⟩
    have hc := h.card_mul_eq (sumClass_uniform σ)
    norm_num [AffinePlane, Fintype.card_prod, ZMod.card] at hc
    omega

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sumClassMatchings_card (σ : AffinePlane) :
    (sumClassMatchings σ).card = if σ = 0 then 4 else 3 := by
  have h : ∀ σ : AffinePlane,
      (sumClassMatchings σ).card = if σ = 0 then 4 else 3 := by
    decide +kernel
  exact h σ

/-- The count is of ordinary perfect matchings, with no assumed completeness. -/
theorem sumClass_perfectMatching_count (σ : AffinePlane) :
    Fintype.card {M : Hypergraph AffinePlane // PerfectMatching (sumClass σ) M} =
      if σ = 0 then 4 else 3 := by
  let f : {M : Hypergraph AffinePlane // PerfectMatching (sumClass σ) M} ≃
      ↥(sumClassMatchings σ) :=
    { toFun := fun M => ⟨M.val, (mem_sumClassMatchings σ M.val).mpr M.property⟩
      invFun := fun M => ⟨M.val, (mem_sumClassMatchings σ M.val).mp M.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr f, Fintype.card_coe]
  exact sumClassMatchings_card σ

/-- Affine lines in the two-dimensional vector space, represented without
choosing a representative for each one-dimensional direction. -/
def affineLine (a b : AffinePlane) : Finset AffinePlane :=
  Finset.univ.image (fun t : ZMod 3 => (a.1 + t * b.1, a.2 + t * b.2))

def affineLines : Hypergraph AffinePlane :=
  Finset.univ.biUnion (fun a : AffinePlane =>
    (Finset.univ.erase 0).image (affineLine a))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem sumClass_zero_eq_affineLines : sumClass 0 = affineLines := by
  decide +kernel

theorem affineLines_card : affineLines.card = 12 := by
  rw [← sumClass_zero_eq_affineLines, sumClass_card]
  simp

end RigidGHZ.Finite
