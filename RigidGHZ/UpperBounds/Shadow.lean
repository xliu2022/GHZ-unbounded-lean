module

public import RigidGHZ.UpperBounds.Average
public import RigidGHZ.UpperBounds.RepresentativeCounts

/-!
# The unrestricted harmonic shadow upper bound

The structural exchange inequality is averaged over all independent choices of
one representative per matching edge. Completion counts identify the conditional
average with the shadow codegree. Finally, all incidences are counted over the
edge-disjoint matching decomposition.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- The contribution of one shadow set in Theorem 4.1. -/
def shadowContribution (r : ℕ) (H : Hypergraph V) (S : Finset V) : ℝ :=
  1 - (1 - 1 / (r : ℝ)) ^ codegree H S

def shadowWeight (r : ℕ) (H : Hypergraph V) (S : Finset V) : ℝ :=
  shadowContribution r H S / codegree H S

/-- Average the reciprocal outdegree at one edge of one matching. -/
theorem average_representative_bound {M : Hypergraph V} {r : ℕ}
    (hH : Uniform H r) (hr : 0 < r) (hM : PerfectMatching H M)
    (b : ∀ e : M, Fin r ≃ e.1) (e : M) :
    finiteAverage (fun q : M → Fin r =>
      1 / (1 + ((Finset.univ.filter
        (exchangeArc H (selectedRepresentative b q) e)).card : ℝ))) ≤
        ∑ v ∈ e.1, shadowWeight r H (e.1.erase v) := by
  classical
  let hit : Fin r → {F : M // F ≠ e} → Finset (Fin r) := otherHits (H := H) b e
  have hfun : (fun q : M → Fin r =>
      (1 : ℝ) / (1 + ((Finset.univ.filter
        (exchangeArc H (selectedRepresentative b q) e)).card : ℝ))) =
      (fun q : M → Fin r =>
        (1 : ℝ) / (1 + (hitCount (hit (q e)) (fun F => q F.1) : ℝ))) := by
    funext q
    rw [selected_outdegree_eq_hitCount]
    rfl
  rw [hfun, finiteAverage_split e
    (fun a q => (1 : ℝ) / (1 + (hitCount (hit a) q : ℝ)))]
  have ha : ∀ a : Fin r,
      finiteAverage (fun q => (1 : ℝ) / (1 + (hitCount (hit a) q : ℝ))) ≤
        (r : ℝ) * shadowWeight r H (e.1.erase (b e a).1) := by
    intro a
    rw [finiteAverage_reciprocal_eq]
    have hb := independent_reciprocal_bound hr (hit a)
    have hc : (∑ F, ((hit a) F).card) + 1 = codegree H (e.1.erase (b e a).1) :=
      sum_otherHits_add_one hH hr hM b e a
    have hcr : ((∑ F, ((hit a) F).card : ℕ) : ℝ) + 1 =
        (codegree H (e.1.erase (b e a).1) : ℝ) := by exact_mod_cast hc
    rw [hc] at hb
    change averageReciprocal (hit a) ≤
      (r : ℝ) * (shadowContribution r H (e.1.erase (b e a).1) /
        codegree H (e.1.erase (b e a).1))
    calc
      _ ≤ (r : ℝ) / (codegree H (e.1.erase (b e a).1) : ℝ) *
          shadowContribution r H (e.1.erase (b e a).1) := by
        simpa only [hcr, shadowContribution] using hb
      _ = _ := by ring
  have hb := finiteAverage_mono _ _ ha
  have hcancel : finiteAverage (fun a : Fin r =>
      (r : ℝ) * shadowWeight r H (e.1.erase (b e a).1)) =
      ∑ a : Fin r, shadowWeight r H (e.1.erase (b e a).1) := by
    unfold finiteAverage
    rw [Fintype.card_fin, ← Finset.mul_sum]
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))
  rw [hcancel] at hb
  calc
    _ ≤ ∑ a : Fin r, shadowWeight r H (e.1.erase (b e a).1) := hb
    _ = ∑ v : e.1, shadowWeight r H (e.1.erase v.1) :=
      (b e).sum_comp (fun v => shadowWeight r H (e.1.erase v.1))
    _ = _ := Finset.sum_coe_sort e.1 (fun v => shadowWeight r H (e.1.erase v))

/-- Averaging the exchange bound in a prescribed perfect matching. -/
theorem matching_shadow_bound {r m : ℕ}
    (G : RigidFamily H I) (i : I) (hH : Uniform H r) (hr : 2 ≤ r)
    (hV : Fintype.card V = r * m) :
    beta m ≤ ∑ e ∈ G.matching i, ∑ v ∈ e, shadowWeight r H (e.erase v) := by
  classical
  have hrpos : 0 < r := by omega
  let b := matchingCoordinates hH (G.perfect i)
  letI : Nonempty (Fin r) := ⟨⟨0, hrpos⟩⟩
  have hm : (G.matching i).card = m := by
    have hc := (G.perfect i).card_mul_eq hH
    rw [hV, Nat.mul_comm r m] at hc
    exact Nat.eq_of_mul_eq_mul_right hrpos hc
  have hq : ∀ q : G.matching i → Fin r,
      beta m ≤ ∑ e : G.matching i,
        1 / (1 + ((Finset.univ.filter
          (exchangeArc H (selectedRepresentative b q) e)).card : ℝ)) := by
    intro q
    rw [← hm]
    apply rigid_exchange_reciprocal_bound G i (selectedRepresentative b q)
      (selectedRepresentative_mem b q)
    intro e
    rw [hH e.1 ((G.perfect i).subset e.2)]
    exact hr
  have hmean := finiteAverage_mono (fun _ : G.matching i → Fin r => beta m) _ hq
  rw [finiteAverage_const, finiteAverage_sum] at hmean
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset (G.matching i)))
    (fun e _ => average_representative_bound hH hrpos (G.perfect i) b e)
  have hh := hmean.trans hsum
  exact hh.trans_eq (Finset.sum_coe_sort (G.matching i)
    (fun e => ∑ v ∈ e, shadowWeight r H (e.erase v)))

/-- The first inequality of Theorem 4.1, before the elementary shadow-size bounds. -/
theorem rigid_harmonic_shadow_bound {r m : ℕ}
    (G : RigidFamily H I) (hH : Uniform H r) (hr : 2 ≤ r)
    (hV : Fintype.card V = r * m) :
    (Fintype.card I : ℝ) * beta m ≤
      ∑ S ∈ shadow H (r - 1), shadowContribution r H S := by
  classical
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset I))
    (fun i _ => matching_shadow_bound G i hH hr hV)
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  have hdis : ((Finset.univ : Finset I) : Set I).PairwiseDisjoint G.matching := by
    intro i hi j hj hij
    exact G.edge_disjoint hij
  have hcount : (∑ i, ∑ e ∈ G.matching i, ∑ v ∈ e, shadowWeight r H (e.erase v)) =
      ∑ S ∈ shadow H (r - 1), shadowContribution r H S := by
    rw [← Finset.sum_biUnion hdis, ← G.covers]
    exact shadow_weight_cancellation hH (by omega) (shadowContribution r H)
  exact hsum.trans_eq hcount

theorem shadow_contribution_sum_le_card {r : ℕ} (hr : 0 < r) :
    (∑ S ∈ shadow H (r - 1), shadowContribution r H S) ≤
      ((shadow H (r - 1)).card : ℝ) := by
  have hbase : (0 : ℝ) ≤ 1 - 1 / (r : ℝ) := by
    have hrreal : (1 : ℝ) ≤ r := by exact_mod_cast hr
    apply sub_nonneg.mpr
    exact (div_le_one (by exact_mod_cast hr)).mpr hrreal
  have hle : ∀ S ∈ shadow H (r - 1), shadowContribution r H S ≤ 1 := by
    intro S _
    exact sub_le_self _ (pow_nonneg hbase _)
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_one] using Finset.sum_le_sum hle

/--
The unrestricted chain of inequalities in Theorem 4.1, for the ordinary notion
of `d`-rigidity and the standard `(r-1)`-shadow.
-/
theorem unrestricted_harmonic_shadow {r m d : ℕ}
    (hR : IsRigid H d) (hH : Uniform H r) (hr : 2 ≤ r)
    (hV : Fintype.card V = r * m) :
    (d : ℝ) * beta m ≤
        ∑ S ∈ shadow H (r - 1), shadowContribution r H S ∧
      (∑ S ∈ shadow H (r - 1), shadowContribution r H S) ≤
        ((shadow H (r - 1)).card : ℝ) ∧
      (shadow H (r - 1)).card ≤ (r * m).choose (r - 1) := by
  obtain ⟨G⟩ := hR
  refine ⟨?_, shadow_contribution_sum_le_card (by omega), ?_⟩
  · simpa only [Fintype.card_fin] using rigid_harmonic_shadow_bound G hH hr hV
  · simpa only [hV] using (shadow_card_le_choose (H := H) (r - 1))

end RigidGHZ.UpperBounds
