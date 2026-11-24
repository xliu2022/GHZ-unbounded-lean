module

public import RigidGHZ.Construction.PackedRectangles

/-! Exact shared-anchor demands for the packed primary rectangles. -/

@[expose] public section

namespace RigidGHZ.Rectangle.PackedLayout

variable {T B H : ℕ} (s : PackedLayout T B H)

def properDemand (l : ℕ) : ℕ :=
  s.nh * (H - 3 * gamma T + l) + s.nv * (B - 2 * T + 1) * l +
    s.nf * (H - 3 * gamma T + (B - 2 * T + 1) * l) +
    s.ns * (s.L - gamma T + (B - 2 * T + 1) * l)

def fullDemand : ℕ :=
  (s.nh + s.nv + s.nf) * gamma T * (T - 1) +
    s.nf * (B - 2 * T) * (H - 3 * gamma T) +
    s.ns * ((B - 2 * T) * (s.L - gamma T) + (T - 1) * gamma T)

 theorem netDemand_sum (l : ℕ) :
    (∑ k, ((s.rectangles k).height - gamma T +
      ((s.rectangles k).width - T + 1) * l)) = s.properDemand l := by
  have hD : 2 * gamma T + gamma T = 3 * gamma T := by omega
  have hT : T + T = 2 * T := by omega
  simp [Index, Fintype.sum_sum_type, rectangles, properDemand, Nat.sub_sub, hD, hT]
  ring

 theorem fullBlock_card (hT : 1 ≤ T) (hB : 2 * T ≤ B) (hH : 3 * gamma T ≤ H)
    (hL : s.ns ≠ 0 → gamma T ≤ s.L) (i : Fin (T + 1)) :
    (ownerBlock s.rectangles i Pattern.full).card = s.fullDemand := by
  rw [ownerBlock_card s.rectangles s.plane_multiple s.separated]
  simp only [Pattern.owners]
  simp_rw [wholeRow_card hT (s.widths_ge hB _) (s.heights_ge hH hL _)]
  have hD : 2 * gamma T + gamma T = 3 * gamma T := by omega
  have hTT : T + T = 2 * T := by omega
  simp [Index, Fintype.sum_sum_type, rectangles, fullDemand, Nat.sub_sub, hD, hTT]
  ring

 theorem prefixBlock_card (hB : 2 * T ≤ B) (hH : 3 * gamma T ≤ H)
    (hL : s.ns ≠ 0 → gamma T ≤ s.L) (i : Fin (T + 1)) (l : Fin T) :
    (ownerBlock s.rectangles i (Pattern.prefix l)).card =
      (residualPool s.rectangles i (Pattern.prefix l)).card + s.properDemand l.val := by
  rw [prefixBlock_net_demand s.rectangles s.plane_multiple s.separated i l
    (s.widths_ge hB) (s.heights_ge hH hL), s.netDemand_sum]

 theorem suffixBlock_card (hB : 2 * T ≤ B) (hH : 3 * gamma T ≤ H)
    (hL : s.ns ≠ 0 → gamma T ≤ s.L) (i : Fin (T + 1)) (l : Fin T) :
    (ownerBlock s.rectangles i (Pattern.suffix l)).card =
      (residualPool s.rectangles i (Pattern.suffix l)).card + s.properDemand l.val := by
  rw [suffixBlock_net_demand s.rectangles s.plane_multiple s.separated i l
    (s.widths_ge hB) (s.heights_ge hH hL), s.netDemand_sum]

 theorem anchor_capacity {A : ℕ} (hT : 1 ≤ T) (hB : 2 * T ≤ B) (hH : 3 * gamma T ≤ H)
    (hL : s.ns ≠ 0 → gamma T ≤ s.L)
    (hfull : s.fullDemand ≤ T * B * H + A * B * gamma T)
    (hproper : ∀ l : Fin T, s.properDemand l.val ≤ A * H + A * B * l.val)
    (i : Fin (T + 1)) (p : Pattern T) :
    (ownerBlock s.rectangles i p).card ≤ RectangleAnchors.externalSupply A B H T p +
      (residualPool s.rectangles i p).card := by
  cases p with
  | full =>
    rw [s.fullBlock_card hT hB hH hL i]
    simp only [RectangleAnchors.externalSupply]
    exact hfull.trans (Nat.le_add_right _ _)
  | «prefix» l =>
    rw [s.prefixBlock_card hB hH hL i l]
    simp only [RectangleAnchors.externalSupply]
    have := hproper l
    omega
  | «suffix» l =>
    rw [s.suffixBlock_card hB hH hL i l]
    simp only [RectangleAnchors.externalSupply]
    have := hproper l
    omega

end RigidGHZ.Rectangle.PackedLayout
