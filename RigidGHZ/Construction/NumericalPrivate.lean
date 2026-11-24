module

public import RigidGHZ.Construction.NumericalDemands

/-! An exact positive integer number of private holes fits in the remaining grid. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Rectangular

open RectangleEstimates Rectangle

theorem grid_lower_real {k T : ℕ} (hk : 1 ≤ k) (hT : 1 ≤ T) :
    4 * (k : ℝ) * ((T : ℝ) - 1) ≤ gridX k T ∧
      6 * (k : ℝ) * ((T : ℝ) - 1) ≤ gridY k T := by
  have hx : ((4 * k * (T - 1) : ℕ) : ℝ) ≤ gridX k T := by
    exact_mod_cast gridX_lower hk hT
  have hy : ((6 * k * (T - 1) : ℕ) : ℝ) ≤ gridY k T := by
    exact_mod_cast gridY_lower hk hT
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_sub hT, Nat.cast_one] using And.intro hx hy

theorem grid_fits {k T H : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    primaryLevels k T H < gridX k T ∧
      gridX k T * (T + 1) < widthA k T ∧ gridY k T * (T + 1) < widthB k T := by
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (224 : ℝ) ≤ T := by exact_mod_cast hT
  have hlevels := primaryLevels_upper hk (by omega) hH
  have hxlow := (grid_lower_real hk (show 1 ≤ T by omega)).1
  have hrem := remaining_levels_lower hkr (show (0 : ℝ) ≤ T by positivity) hxlow hlevels
  have hrempos : (0 : ℝ) < (k : ℝ) * ((13 / 24 : ℝ) * T - 10) :=
    mul_pos (by linarith) (by linarith)
  have hlt : (primaryLevels k T H : ℝ) < gridX k T := by linarith
  have hX := Nat.div_mul_le_self (widthA k T - 1) (T + 1)
  have hY := Nat.div_mul_le_self (widthB k T - 1) (T + 1)
  change gridX k T * (T + 1) ≤ widthA k T - 1 at hX
  change gridY k T * (T + 1) ≤ widthB k T - 1 at hY
  have hwp := widths_pos hk (show 1 ≤ T by omega)
  refine ⟨by exact_mod_cast hlt, ?_, ?_⟩ <;> omega

theorem numericalLayout_plane_fit {k T H : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H) :
    primaryLevels k T H * (T + 1) < widthA k T := by
  have hg := grid_fits hk hT hH
  exact (Nat.mul_le_mul_right (T + 1) hg.1.le).trans_lt hg.2.1

theorem private_count_exists {k T H ρ : ℕ} (hk : 1 ≤ k) (hT : 224 ≤ T)
    (hH : (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 - 2 ≤ H)
    (hH' : (H : ℝ) ≤ (16 / 3 : ℝ) * k * (T : ℝ) ^ 3 + 39 * k * (T : ℝ) ^ 2)
    (hρ : ρ < widthA k T * widthB k T) :
    ∃ R : ℕ, 0 < R ∧
      R ≤ (gridX k T - primaryLevels k T H) * gridY k T * (H - 2 * gamma T) ∧
      (widthA k T + T) * (widthB k T + T) * (H + 2 * gamma T + 1) =
        (numericalLayout k T H hk (by omega) hH).area + R +
          (widthA k T * widthB k T * H + ρ + 1) ∧
      (R : ℝ) ≤ (46 / 3 : ℝ) * k * (T : ℝ) ^ 5 + 80 * (k : ℝ) ^ 2 * (T : ℝ) ^ 4 := by
  let s := numericalLayout k T H hk (by omega) hH
  let volume := (widthA k T + T) * (widthB k T + T) * (H + 2 * gamma T + 1)
  let size := widthA k T * widthB k T * H + ρ + 1
  let R := volume - s.area - size
  have hkr : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hTr : (224 : ℝ) ≤ T := by exact_mod_cast hT
  have hρplus : ((ρ + 1 : ℕ) : ℝ) ≤ (widthA k T : ℝ) * widthB k T := by exact_mod_cast hρ
  have hρr : (ρ : ℝ) ≤ A k T * B k T - 1 := by
    rw [← widthA_cast, ← widthB_cast]
    push_cast at hρplus
    linarith
  have hprivate := privateAmount_bounds hkr (show (100 : ℝ) ≤ T by linarith)
    hH hH' (Nat.cast_nonneg ρ) hρr
  have he : (volume : ℝ) - s.area - size = privateAmount k T H ρ := by
    rw [show (s.area : ℝ) = roundedArea k T H from numericalLayout_area_cast k T H hk _ hH]
    simp only [volume, size, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one,
      widthA_cast, widthB_cast, gamma_cast, privateAmount]
  have hpos : (0 : ℝ) < (volume : ℝ) - s.area - size := by rw [he]; exact hprivate.1
  have hsum : s.area + size < volume := by
    exact_mod_cast (show (s.area : ℝ) + size < volume by linarith only [hpos])
  have hRcast : (R : ℝ) = privateAmount k T H ρ := by
    change ((volume - s.area - size : ℕ) : ℝ) = _
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    exact he
  have hRpos : 0 < R := by exact_mod_cast (show (0 : ℝ) < R by rw [hRcast]; exact hprivate.1)
  have hRupper : (R : ℝ) ≤ (46 / 3 : ℝ) * k * (T : ℝ) ^ 5 +
      80 * (k : ℝ) ^ 2 * (T : ℝ) ^ 4 := by rw [hRcast]; exact hprivate.2
  have hgrid := grid_fits hk hT hH
  have hgridlower := grid_lower_real hk (show 1 ≤ T by omega)
  have hcap := private_grid_capacity hkr hTr hH (primaryLevels_upper hk (by omega) hH)
    hgridlower.1 hgridlower.2 hRupper
  have hHm : 2 * gamma T ≤ H := by have h := (natural_margins hk (by omega) hH).2; omega
  have hcapNat : R ≤ (gridX k T - primaryLevels k T H) * gridY k T * (H - 2 * gamma T) := by
    have hc : (R : ℝ) < ((gridX k T - primaryLevels k T H) * gridY k T *
        (H - 2 * gamma T) : ℕ) := by
      simpa only [Nat.cast_mul, Nat.cast_sub hgrid.1.le, Nat.cast_sub hHm,
        Nat.cast_ofNat, gamma_cast] using hcap
    exact_mod_cast hc.le
  refine ⟨R, hRpos, hcapNat, ?_, hRupper⟩
  change volume = s.area + (volume - s.area - size) + size
  omega

end RigidGHZ.Rectangular
