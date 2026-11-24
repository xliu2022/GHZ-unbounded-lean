module

public import RigidGHZ.UpperBounds.Corollaries

/-! The elementary vertex-degree bounds stated before the harmonic refinement. -/

@[expose] public section

namespace RigidGHZ.UpperBounds

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Deleting a fixed incident vertex injects incident `r`-edges into the
`(r-1)`-subsets of the remaining vertices. -/
theorem uniform_degree_le_choose {H : Hypergraph V} {r : ℕ}
    (hH : Uniform H r) (v : V) :
    degree H v ≤ (Fintype.card V - 1).choose (r - 1) := by
  classical
  let S := H.filter (fun e => v ∈ e)
  have hinj : Set.InjOn (fun e : Finset V => e.erase v) S := by
    intro e he f hf hef
    exact Finset.erase_injOn' v (Finset.mem_filter.mp he).2
      (Finset.mem_filter.mp hf).2 hef
  have hsub : S.image (fun e => e.erase v) ⊆
      (Finset.univ.erase v).powersetCard (r - 1) := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    have hfH := (Finset.mem_filter.mp hf).1
    have hvf := (Finset.mem_filter.mp hf).2
    apply Finset.mem_powersetCard.mpr
    constructor
    · intro w hw
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hw).1, Finset.mem_univ _⟩
    · rw [Finset.card_erase_of_mem hvf, hH f hfH]
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj, Finset.card_powersetCard] at hc
  simpa [S, degree] using hc

theorem rigid_dimension_le_choose [Nonempty V] {H : Hypergraph V} {r d : ℕ}
    (hH : Uniform H r) (hR : IsRigid H d) :
    d ≤ (Fintype.card V - 1).choose (r - 1) := by
  classical
  obtain ⟨R⟩ := hR
  let v : V := Classical.arbitrary V
  have h := uniform_degree_le_choose hH v
  simpa only [R.regular v, Fintype.card_fin] using h

theorem one_le_beta {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) ≤ beta m := by
  by_cases he : m = 1
  · simp [beta, he]
  · rw [beta, if_neg he]
    apply le_min
    · have hm2 : (2 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (show 2 ≤ m by omega)
      norm_num
      linarith
    · exact harmonic_ge_one hm

theorem balanced_dimension_le_power {H : Hypergraph V} {r m d : ℕ}
    (hr : 2 ≤ r) (hm : 1 ≤ m) (hP : BalancedPartite H r m) (hR : IsRigid H d) :
    d ≤ m ^ (r - 1) := by
  have h := balanced_partite_harmonic_bound hr hR hP
  have hle : (d : ℝ) ≤ (d : ℝ) * beta m := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (one_le_beta hm) (Nat.cast_nonneg d)
  exact_mod_cast hle.trans h

end RigidGHZ.UpperBounds
