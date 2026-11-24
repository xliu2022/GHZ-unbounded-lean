module

public import RigidGHZ.Construction.NumericalPrivate
public import RigidGHZ.Construction.PackedFactor
public import RigidGHZ.Construction.GrowthAssembly

/-!
# The unconditional rectangular construction

The only hypotheses are the paper's integer parameter range. All finite
geometric data, capacities, tags, and perfect matchings are constructed below.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

def SupportedRectangularFactor (k T m : ℕ) : Prop :=
    ∃ G : Hypergraph (Fin 3 × Fin m), ∃ U : Finset (Fin m),
      Uniform G 3 ∧ BalancedPartite G 3 m ∧
      Nonempty (RigidFamily G (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ G, ∃ x : Fin 3 → Fin m, e = tupleEdge x) ∧
      (∀ x : Fin 3 → Fin m, tupleEdge x ∈ G →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) ∧
      k * U.card ≤ m

theorem rectangular_factor {k T m : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hlo : 128 * k ^ 3 * T ^ 7 ≤ m) (hhi : m < 128 * k ^ 3 * (T + 1) ^ 7) :
    SupportedRectangularFactor k T m := by
  classical
  let H := boxHeight k T m
  let ρ := remainder k T m
  have hT6 : 6 ≤ T := by omega
  have hm : 1 ≤ m := by
    have hp : 0 < 128 * k ^ 3 * T ^ 7 := by positivity
    omega
  have hdiv := box_division (T := T) hk (show 1 ≤ T by omega) hm
  have hρ : ρ < widthA k T * widthB k T := hdiv.1
  have hsize : widthA k T * widthB k T * H + ρ + 1 = m := hdiv.2
  have hheight := box_height_bounds hk (show 100 ≤ T by omega) hlo hhi
  have hh : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H := hheight.1
  have hh' : (H : ℝ) ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2 := hheight.2
  let s := numericalLayout k T H hk hT6 hh
  obtain ⟨R, hRpos, hRcap, hbalance, hRupper⟩ := private_count_exists hk hT hh hh' hρ
  have hmarg := natural_margins hk hT6 hh
  have hgrid := grid_fits hk hT hh
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (6 : ℝ) ≤ T := by exact_mod_cast hT6
  have hnh : 0 < s.nh := by
    have hn := (nHorizontal_bounds hkr hTr hh).1
    change 0 < nHorizontal k T H
    omega
  have hnf : 0 < s.nf := by
    have hn := (nFull_bounds hkr hTr hh).1
    change 0 < nFull k T H
    omega
  obtain ⟨G, U, hUG, hPG, hRG, htrans, hsupport, hUcard⟩ :=
    s.factor_of_counts (A := widthA k T) (Px := gridX k T) (Py := gridY k T)
      (R := R) (ρ := ρ) (show 1 ≤ T by omega) hmarg.1 hmarg.2
      (shortIndicator_valid k T H) hnh hnf (numericalLayout_plane_fit hk hT hh)
      hgrid.2.1 hgrid.2.2 hRpos hRcap hρ.le
      (numericalLayout_full_supply k T H hk hT6 hh)
      (fun l => numericalLayout_proper_supply k T H l.val hk hT6 hh) hbalance
  have hbound : k * U.card ≤ widthA k T * widthB k T * H + ρ + 1 := by
    by_cases hk1 : k = 1
    · simpa only [hk1, one_mul, Fintype.card_fin] using Finset.card_le_univ U
    · have hk2 : 2 ≤ k := by omega
      have hk2r : (2 : ℝ) ≤ k := by exact_mod_cast hk2
      have hT100 : (100 : ℝ) ≤ T := by exact_mod_cast (show 100 ≤ T by omega)
      have hh5 := height_margin hkr hTr hh
      have hd := D_nonneg (show (1 : ℝ) ≤ T by linarith)
      have hh5' : 5 * (k : ℝ) * (T : ℝ) ^ 3 ≤ H := by linarith
      have hu : (U.card : ℝ) ≤ 1 + ((T : ℝ) + 1) * primaryLevels k T H * B k T * H +
          ((T : ℝ) + 1) ^ 2 * R := by
        have hu' : (U.card : ℝ) ≤ 1 + ((T : ℝ) + 1) * s.totalLevels * (widthB k T : ℝ) * H +
            ((T : ℝ) + 1) ^ 2 * R := by exact_mod_cast hUcard
        simpa only [s, numericalLayout_levels, widthB_cast] using hu'
      have harea : A k T * B k T * H ≤
          ((widthA k T * widthB k T * H + ρ + 1 : ℕ) : ℝ) := by
        rw [← widthA_cast, ← widthB_cast]
        exact_mod_cast (show widthA k T * widthB k T * H ≤
          widthA k T * widthB k T * H + ρ + 1 by omega)
      have hb := RectangleEstimates.active_support_lt hk2r hT100 hh5'
        (primaryLevels_upper hk hT6 hh) hRupper hu harea
      exact_mod_cast hb.le
  have result : ∃ G : Hypergraph (Fin 3 × Fin (widthA k T * widthB k T * H + ρ + 1)),
      ∃ U : Finset (Fin (widthA k T * widthB k T * H + ρ + 1)),
      Uniform G 3 ∧ BalancedPartite G 3 (widthA k T * widthB k T * H + ρ + 1) ∧
      Nonempty (RigidFamily G (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ G, ∃ x : Fin 3 → Fin (widthA k T * widthB k T * H + ρ + 1), e = tupleEdge x) ∧
      (∀ x : Fin 3 → Fin (widthA k T * widthB k T * H + ρ + 1), tupleEdge x ∈ G →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U)) ∧
      k * U.card ≤ widthA k T * widthB k T * H + ρ + 1 :=
    ⟨G, U, hUG, hPG, hRG, htrans, hsupport, hbound⟩
  exact (congrArg (SupportedRectangularFactor k T) hsize).mp result

theorem rectangular_product {k T m : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hlo : 128 * k ^ 3 * T ^ 7 ≤ m) (hhi : m < 128 * k ^ 3 * (T + 1) ^ 7) :
    Growth.ExistsRigid (k + 2) m ((T + 1) ^ (2 * k)) := by
  obtain ⟨G, U, hUG, hPG, ⟨R⟩, htrans, hsupport, hbound⟩ := rectangular_factor hk hT hlo hhi
  have h := Growth.product_of_factor_card (k := k) (q := (T + 1) ^ 2)
    (by simp : Fintype.card (Fin m) = m)
    (by simp [pow_two] : Fintype.card (Fin (T + 1) × Fin (T + 1)) = (T + 1) ^ 2)
    G R U hbound htrans hsupport
  simpa only [← pow_mul] using h

end RigidGHZ.Rectangular
