module

public import RigidGHZ.UpperBounds.FiniteAverage
public import Mathlib.Data.Finset.Powerset

/-! Finite shadow incidence and completion identities. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

variable {V : Type*} [DecidableEq V] {H : Hypergraph V}

/-- The `k`-shadow of a finite hypergraph. -/
def shadow (H : Hypergraph V) (k : ℕ) : Finset (Finset V) :=
  H.biUnion (fun e => e.powersetCard k)

/-- Number of hyperedges containing the specified set. -/
def codegree (H : Hypergraph V) (S : Finset V) : ℕ :=
  (H.filter (fun e => S ⊆ e)).card

theorem mem_shadow {k : ℕ} {S : Finset V} :
    S ∈ shadow H k ↔ S.card = k ∧ ∃ e ∈ H, S ⊆ e := by
  simp only [shadow, Finset.mem_biUnion, Finset.mem_powersetCard]
  constructor
  · rintro ⟨e, he, hsub, hc⟩
    exact ⟨hc, e, he, hsub⟩
  · rintro ⟨hc, e, he, hsub⟩
    exact ⟨e, he, hsub, hc⟩

theorem codegree_pos_of_mem_shadow {k : ℕ} {S : Finset V}
    (hS : S ∈ shadow H k) : 0 < codegree H S := by
  obtain ⟨_, e, he, hsub⟩ := mem_shadow.mp hS
  exact Finset.card_pos.mpr ⟨e, Finset.mem_filter.mpr ⟨he, hsub⟩⟩

theorem exists_completion_vertex {e S : Finset V}
    (hsub : S ⊆ e) (hcard : S.card + 1 = e.card) :
    ∃ v, v ∈ e ∧ v ∉ S ∧ insert v S = e := by
  have hdiff : (e \ S).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub, ← hcard]
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hdiff
  have hvmem : v ∈ e \ S := by rw [hv]; simp
  have hset := Finset.sdiff_union_of_subset hsub
  rw [hv, Finset.singleton_union] at hset
  exact ⟨v, (Finset.mem_sdiff.mp hvmem).1, (Finset.mem_sdiff.mp hvmem).2, hset⟩

theorem completion_not_mem {r : ℕ} (hH : Uniform H r) (hr : 0 < r)
    {S : Finset V} (hS : S.card = r - 1) {v : V} (hv : insert v S ∈ H) : v ∉ S := by
  intro hmem
  have hc := hH _ hv
  rw [Finset.insert_eq_of_mem hmem, hS] at hc
  omega

theorem image_erases_eq_powersetCard {e : Finset V} {r : ℕ}
    (he : e.card = r) (hr : 0 < r) :
    e.image e.erase = e.powersetCard (r - 1) := by
  classical
  ext S
  constructor
  · intro hS
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hS
    exact Finset.mem_powersetCard.mpr
      ⟨Finset.erase_subset _ _, by rw [Finset.card_erase_of_mem hv, he]⟩
  · intro hS
    have hh := Finset.mem_powersetCard.mp hS
    obtain ⟨v, hv, hvS, hve⟩ := exists_completion_vertex hh.1 (by omega)
    apply Finset.mem_image.mpr
    refine ⟨v, hv, ?_⟩
    rw [← hve, Finset.erase_insert hvS]

theorem sum_erases_eq_sum_powersetCard {e : Finset V} {r : ℕ}
    (he : e.card = r) (hr : 0 < r) (f : Finset V → ℝ) :
    (∑ v ∈ e, f (e.erase v)) = ∑ S ∈ e.powersetCard (r - 1), f S := by
  rw [← image_erases_eq_powersetCard he hr, Finset.sum_image]
  exact fun u hu v hv huv => (Finset.erase_inj e hu).mp huv

/-- Double-counting incidences between edges and members of the shadow. -/
theorem shadow_incidence_sum (k : ℕ) (f : Finset V → ℝ) :
    (∑ e ∈ H, ∑ S ∈ e.powersetCard k, f S) =
      ∑ S ∈ shadow H k, (codegree H S : ℝ) * f S := by
  classical
  have hfilt : ∀ e ∈ H,
      (shadow H k).filter (fun S => S ⊆ e) = e.powersetCard k := by
    intro e he
    ext S
    constructor
    · intro hS
      have hs := Finset.mem_filter.mp hS
      exact Finset.mem_powersetCard.mpr ⟨hs.2, (mem_shadow.mp hs.1).1⟩
    · intro hS
      have hs := Finset.mem_powersetCard.mp hS
      exact Finset.mem_filter.mpr ⟨mem_shadow.mpr ⟨hs.2, e, he, hs.1⟩, hs.1⟩
  calc
    _ = ∑ e ∈ H, ∑ S ∈ shadow H k, if S ⊆ e then f S else 0 := by
      apply Finset.sum_congr rfl
      intro e he
      rw [← hfilt e he, Finset.sum_filter]
    _ = ∑ S ∈ shadow H k, ∑ e ∈ H, if S ⊆ e then f S else 0 :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, codegree]

theorem shadow_weight_cancellation {r : ℕ} (hH : Uniform H r) (hr : 0 < r)
    (f : Finset V → ℝ) :
    (∑ e ∈ H, ∑ v ∈ e, f (e.erase v) / (codegree H (e.erase v) : ℝ)) =
      ∑ S ∈ shadow H (r - 1), f S := by
  have hsum : (∑ e ∈ H, ∑ v ∈ e,
      f (e.erase v) / (codegree H (e.erase v) : ℝ)) =
      ∑ e ∈ H, ∑ S ∈ e.powersetCard (r - 1), f S / (codegree H S : ℝ) := by
    apply Finset.sum_congr rfl
    intro e he
    exact sum_erases_eq_sum_powersetCard (hH e he) hr (fun S => f S / (codegree H S : ℝ))
  rw [hsum, shadow_incidence_sum]
  apply Finset.sum_congr rfl
  intro S hS
  exact mul_div_cancel₀ (f S) (Nat.cast_ne_zero.mpr (Nat.ne_of_gt (codegree_pos_of_mem_shadow hS)))

theorem shadow_card_le_choose [Fintype V] (k : ℕ) :
    (shadow H k).card ≤ (Fintype.card V).choose k := by
  have hsub : shadow H k ⊆ Finset.univ.powersetCard k := by
    intro S hS
    exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, (mem_shadow.mp hS).1⟩
  simpa only [Finset.card_powersetCard, Finset.card_univ] using Finset.card_le_card hsub

end RigidGHZ.UpperBounds
