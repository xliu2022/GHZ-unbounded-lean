module

public import RigidGHZ.SourceModel.JointState

/-! Exact photon-number selection for sources with arbitrary nonnegative
integer emission multiplicities.  Only the coefficients at multiplicities
zero and one survive.  No truncation assumption on the source is needed. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.SourceModel

open scoped BigOperators

variable {V I : Type*} [DecidableEq V] {H : Hypergraph V}

def multiplePhotonCount (H : Hypergraph V) (k : Finset V → ℕ) (v : V) : ℕ :=
  ∑ e ∈ H, if v ∈ e then k e else 0

def MultipleAccepted (H : Hypergraph V) (k : Finset V → ℕ) : Prop :=
  ∀ v, multiplePhotonCount H k v = 1

def emittingEdges (H : Hypergraph V) (k : Finset V → ℕ) : Hypergraph V :=
  H.filter (fun e => 0 < k e)

theorem multiplicity_le_photonCount (k : Finset V → ℕ) {e : Finset V}
    (he : e ∈ H) {v : V} (hv : v ∈ e) : k e ≤ multiplePhotonCount H k v := by
  have h := Finset.single_le_sum (fun f (_ : f ∈ H) =>
    Nat.zero_le (if v ∈ f then k f else 0)) he
  simpa only [multiplePhotonCount, ite_eq_left hv] using h

theorem accepted_multiplicity_le_one (k : Finset V → ℕ)
    (hn : ∀ e ∈ H, e.Nonempty) (ha : MultipleAccepted H k) :
    ∀ e ∈ H, k e ≤ 1 := by
  intro e he
  obtain ⟨v, hv⟩ := hn e he
  exact (multiplicity_le_photonCount k he hv).trans_eq (ha v)

/-- A source with multiplicity at least two is rejected by exact path counts. -/
theorem multiple_emission_rejected (k : Finset V → ℕ)
    {e : Finset V} (he : e ∈ H) (hne : e.Nonempty) (hk : 2 ≤ k e) :
    ¬ MultipleAccepted H k := by
  obtain ⟨v, hv⟩ := hne
  intro ha
  have h := (multiplicity_le_photonCount k he hv).trans_eq (ha v)
  omega

theorem multiplePhotonCount_eq_card (k : Finset V → ℕ)
    (hk : ∀ e ∈ H, k e ≤ 1) (v : V) :
    multiplePhotonCount H k v = ((emittingEdges H k).filter (fun e => v ∈ e)).card := by
  simp only [multiplePhotonCount, emittingEdges, Finset.filter_filter,
    Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  have h := hk e he
  by_cases hv : v ∈ e <;> by_cases hz : 0 < k e <;> simp [hv, hz] <;> omega

/-- Accepted arbitrary-multiplicity patterns are precisely binary patterns
whose emitting sources form an ordinary perfect matching. -/
theorem multipleAccepted_iff (k : Finset V → ℕ) (hn : ∀ e ∈ H, e.Nonempty) :
    MultipleAccepted H k ↔
      (∀ e ∈ H, k e ≤ 1) ∧ PerfectMatching H (emittingEdges H k) := by
  constructor
  · intro ha
    have hk := accepted_multiplicity_le_one k hn ha
    refine ⟨hk, Finset.filter_subset _ _, ?_⟩
    intro v
    rw [← multiplePhotonCount_eq_card k hk v]
    exact ha v
  · rintro ⟨hk, hM⟩ v
    rw [multiplePhotonCount_eq_card k hk v]
    exact hM.2 v

def multiplePatternAmplitude (c : Finset V → ℕ → ℂ) (k : Finset V → ℕ) : ℂ :=
  ∏ e ∈ H, c e (k e)

def multipleMatchingAmplitude (c : Finset V → ℕ → ℂ) (M : PerfectMatchings H) : ℂ :=
  (∏ e ∈ M.1, c e 1) * ∏ e ∈ H \ M.1, c e 0

/-- The exact coefficient of an accepted term uses only `c[e,1]` and `c[e,0]`. -/
theorem multiplePatternAmplitude_eq (c : Finset V → ℕ → ℂ) (k : Finset V → ℕ)
    (hk : ∀ e ∈ H, k e ≤ 1) :
    multiplePatternAmplitude (H := H) c k =
      (∏ e ∈ emittingEdges H k, c e 1) * ∏ e ∈ H \ emittingEdges H k, c e 0 := by
  have hs : emittingEdges H k ⊆ H := Finset.filter_subset _ _
  rw [multiplePatternAmplitude, ← Finset.prod_sdiff hs, mul_comm]
  congr 1
  · apply Finset.prod_congr rfl
    intro e he
    obtain ⟨heH, hepos⟩ := Finset.mem_filter.mp he
    have : k e = 1 := by have := hk e heH; omega
    rw [this]
  · apply Finset.prod_congr rfl
    intro e he
    obtain ⟨heH, heout⟩ := Finset.mem_sdiff.mp he
    have : k e = 0 := by
      have : ¬ 0 < k e := fun h => heout (Finset.mem_filter.mpr ⟨heH, h⟩)
      omega
    rw [this]

theorem accepted_multiple_amplitude (c : Finset V → ℕ → ℂ) (k : Finset V → ℕ)
    (hn : ∀ e ∈ H, e.Nonempty) (ha : MultipleAccepted H k) :
    multiplePatternAmplitude (H := H) c k =
      multipleMatchingAmplitude c ⟨emittingEdges H k, ((multipleAccepted_iff k hn).mp ha).2⟩ :=
  multiplePatternAmplitude_eq c k (accepted_multiplicity_le_one k hn ha)

theorem multipleMatchingAmplitude_normSq [Fintype V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hU : Uniform H r) (hr : 0 < r)
    (hV : Fintype.card V = r * m) (c : Finset V → ℕ → ℂ) (p0 p1 : ℝ)
    (hc0 : ∀ e ∈ H, Complex.normSq (c e 0) = p0)
    (hc1 : ∀ e ∈ H, Complex.normSq (c e 1) = p1)
    (M : PerfectMatchings H) :
    Complex.normSq (multipleMatchingAmplitude c M) = p1 ^ m * p0 ^ (m * (d - 1)) := by
  rw [multipleMatchingAmplitude, Complex.normSq_mul, map_prod, map_prod]
  have hcard : H.card = d * m := by simpa using G.card_edges hU hr hV
  have hm := perfectMatching_card hU hr hV M
  have he : d * m - m = m * (d - 1) := by
    rw [Nat.mul_sub_left_distrib, Nat.mul_one, Nat.mul_comm m d]
  have h1 : (∏ e ∈ M.val, Complex.normSq (c e 1)) = p1 ^ m := by
    calc
      _ = ∏ _e ∈ M.val, p1 := Finset.prod_congr rfl (fun e he => hc1 e (M.property.subset he))
      _ = _ := by simp [hm]
  have h0 : (∏ e ∈ H \ M.val, Complex.normSq (c e 0)) = p0 ^ (m * (d - 1)) := by
    calc
      _ = ∏ _e ∈ H \ M.val, p0 :=
        Finset.prod_congr rfl (fun e he => hc0 e (Finset.mem_sdiff.mp he).1)
      _ = _ := by simp [Finset.card_sdiff_of_subset M.property.subset, hcard, hm, he]
  rw [h1, h0]

/-- The identical-source formula after arbitrary-multiplicity postselection. -/
theorem identical_multiple_success [Fintype V] [Nonempty V] {r m d : ℕ}
    (G : RigidFamily H (Fin d)) (hU : Uniform H r) (hr : 0 < r)
    (hV : Fintype.card V = r * m) (c : Finset V → ℕ → ℂ) (p0 p1 : ℝ)
    (hc0 : ∀ e ∈ H, Complex.normSq (c e 0) = p0)
    (hc1 : ∀ e ∈ H, Complex.normSq (c e 1) = p1) :
    stateNormSq ((MatchingDecomposition.ofRigidFamily G).acceptedState
      (multipleMatchingAmplitude c)) = (d : ℝ) * p1 ^ m * p0 ^ (m * (d - 1)) := by
  rw [stateNormSq, MatchingDecomposition.acceptedState,
    finitePushforward_normSq _ _
      ((MatchingDecomposition.ofRigidFamily G).labelString_injective
        (nonempty_edges_of_uniform hU hr))]
  simp_rw [multipleMatchingAmplitude_normSq G hU hr hV c p0 p1 hc0 hc1]
  have hcard : Fintype.card (PerfectMatchings H) = d := by
    simpa using perfectMatchings_card G
  simp [hcard, mul_assoc]

end RigidGHZ.SourceModel
