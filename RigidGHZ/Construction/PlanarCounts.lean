module

public import RigidGHZ.Construction.PlanarHoles

/-! Exact finite cardinalities for the planar holes and external anchor pools. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

theorem box_card_int {lx ux ly uy : ℤ} (hx : lx ≤ ux) (hy : ly ≤ uy) :
    ((box lx ux ly uy).card : ℤ) = (ux - lx) * (uy - ly) := by
  simp only [box, Finset.card_product, Int.card_Ico, Nat.cast_mul,
    Int.toNat_of_nonneg (sub_nonneg.mpr hx), Int.toNat_of_nonneg (sub_nonneg.mpr hy)]

def natEmbedding : (ℕ × ℕ) ↪ Lattice where
  toFun x := (x.1, x.2)
  inj' := by
    intro x y h
    have hh : x.1 = y.1 ∧ x.2 = y.2 := by
      simpa only [Prod.mk.injEq, Nat.cast_inj] using h
    exact Prod.ext hh.1 hh.2

theorem tagRectangle_eq_map (w h b : ℕ) :
    tagRectangle w h b = (rectangle w (h + 1) b).map natEmbedding := by
  ext x
  simp only [tagRectangle, box, rectangle, Finset.mem_product, Finset.mem_Ico,
    Finset.mem_map, natEmbedding, Function.Embedding.coeFn_mk]
  constructor
  · intro hx
    refine ⟨(x.1.toNat, x.2.toNat), ?_, ?_⟩
    · have hx0 : 0 ≤ x.1 := by omega
      have hy0 : 0 ≤ x.2 := by omega
      have hxcast := Int.toNat_of_nonneg hx0
      have hycast := Int.toNat_of_nonneg hy0
      dsimp
      omega
    · dsimp
      exact Prod.ext (Int.toNat_of_nonneg (by omega)) (Int.toNat_of_nonneg (by omega))
  · rintro ⟨⟨a, c⟩, hx, hxe⟩
    cases hxe
    dsimp at hx ⊢
    omega

theorem tagRegion_eq_map (w h T : ℕ) :
    tagRegion w h T = (rectangleUnion w (h + 1) T).map natEmbedding := by
  ext x
  simp only [tagRegion, rectangleUnion, Finset.mem_biUnion, Finset.mem_map,
    tagRectangle_eq_map]
  constructor
  · rintro ⟨b, hb, y, hy, he⟩
    exact ⟨y, ⟨b, hb, hy⟩, he⟩
  · rintro ⟨y, ⟨b, hb, hy⟩, he⟩
    exact ⟨b, hb, y, hy, he⟩

theorem tagRegion_card {w h T : ℕ} (hw : 1 ≤ w) (hh : T ≤ h + 2) :
    (tagRegion w h T).card = (w + T) * (h + 1) + (w - 1) * gamma T := by
  rw [tagRegion_eq_map, Finset.card_map]
  exact rectangleUnion_card w (h + 1) T hw hh

theorem primaryOne_card {w h T : ℕ} (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    ((primaryOne w h T).card : ℤ) = T * h + ((w : ℤ) - 3 * T) * gamma T := by
  have hd : Disjoint (box T (2 * T) (gamma T) h)
      (box (2 * T) w (gamma T) (2 * gamma T)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  rw [primaryOne, Finset.card_union_of_disjoint hd, Nat.cast_add,
    box_card_int (by omega) (by omega), box_card_int (by omega) (by omega)]
  push_cast
  ring

theorem primaryTwo_card (T : ℕ) :
    ((primaryTwo T).card : ℤ) = T * auxiliaryHeight T := by
  rw [primaryTwo, box_card_int (by omega) (by omega)]
  push_cast
  ring

theorem firstOwnerEnvelope_card {w h T : ℕ} (hw : 2 * T ≤ w) :
    ((firstOwnerEnvelope w h T).card : ℤ) =
      2 * T * h + 2 * gamma T * ((w : ℤ) - 2 * T) := by
  have hd : Disjoint (box 0 (2 * T) 0 h) (box (2 * T) w 0 (2 * gamma T)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  rw [firstOwnerEnvelope, Finset.card_union_of_disjoint hd, Nat.cast_add,
    box_card_int (by omega) (by omega), box_card_int (by omega) (by omega)]
  push_cast
  ring

theorem secondOwnerEnvelope_card (T : ℕ) :
    ((secondOwnerEnvelope T).card : ℤ) = 2 * T * (gamma T + auxiliaryHeight T) := by
  rw [secondOwnerEnvelope, box_card_int (by omega) (by omega)]
  push_cast
  ring

def sigma (w h T j : ℕ) : ℤ :=
  (h : ℤ) - 2 * gamma T + gamma j + ((w : ℤ) - 2 * T + j - 1) * (j - 1)

theorem firstSuffixOwners_card {w h T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    ((firstSuffixOwners w h T j).card : ℤ) = sigma w h T j := by
  have hgj := gamma_int_mono hjT
  have hgjp := gamma_int_mono (show j - 1 ≤ j by omega)
  have hjpred : j - 1 + 1 = j := by omega
  have hg := gamma_int_succ (j - 1)
  rw [hjpred] at hg
  have hpred : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  rw [hpred] at hg
  rw [firstSuffixOwners_boxes hj hjT hw hh]
  have hd : Disjoint
      (box ((T : ℤ) - j) ((T : ℤ) - j + 1) ((gamma T : ℤ) - gamma j) ((h : ℤ) - gamma T))
      (box ((T : ℤ) - j + 1) ((w : ℤ) - T) ((gamma T : ℤ) - gamma j)
        ((gamma T : ℤ) - gamma (j - 1))) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  rw [Finset.card_union_of_disjoint hd, Nat.cast_add,
    box_card_int (by omega) (by omega), box_card_int (by omega) (by omega)]
  dsimp [sigma]
  rw [show (gamma (j - 1) : ℤ) = gamma j - (j - 1) by omega]
  ring

def prefixPool (w h T j : ℕ) : Finset Lattice :=
  prefixColumn w h T j ∪ prefixStrip w h T j

def lowerPool (w T j : ℕ) : Finset Lattice :=
  (Finset.range T).biUnion (fun a => lowerColumn w a j)

def suffixPool (w h T j : ℕ) : Finset Lattice :=
  suffixColumn w h T j ∪ suffixStrip w h T j ∪ lowerPool w T j

def externalDemand (w h T j : ℕ) : ℤ :=
  (h : ℤ) - T + 2 + ((w : ℤ) - T) * (j - 1)

theorem prefixPool_card {w h T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) (hw : T ≤ w) :
    ((prefixPool w h T j).card : ℤ) = externalDemand w h T j + T - 1 := by
  have hd : Disjoint (prefixColumn w h T j) (prefixStrip w h T j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [prefixColumn, prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  have hg := gamma_int_succ (j - 1)
  rw [show j - 1 + 1 = j by omega] at hg
  have hgm := gamma_int_mono (show j - 1 ≤ j by omega)
  rw [prefixPool, Finset.card_union_of_disjoint hd, Nat.cast_add]
  unfold prefixColumn prefixStrip
  rw [box_card_int (by omega) (by omega), box_card_int (by omega) (by omega)]
  have hpred : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  rw [hpred] at hg
  dsimp [externalDemand]
  rw [show (gamma (j - 1) : ℤ) = gamma j - (j - 1) by omega]
  ring

theorem lowerColumn_card (w a j : ℕ) (hj : 1 ≤ j) :
    ((lowerColumn w a j).card : ℤ) = min a (j - 1) := by
  have hm := rise_mono a (show j - 1 ≤ j by omega)
  have hs := rise_succ a (j - 1)
  rw [show j - 1 + 1 = j by omega] at hs
  rw [lowerColumn, box_card_int (by omega) (by omega)]
  linarith


theorem sum_range_id (T : ℕ) : ∑ a ∈ Finset.range T, a = gamma T := by
  induction T with
  | zero => simp
  | succ T ih => rw [Finset.sum_range_succ, ih, gamma_succ]

theorem sum_min {T l : ℕ} (hl : l ≤ T) :
    ∑ a ∈ Finset.range T, min a l = gamma l + (T - l) * l := by
  have hsplit : T = l + (T - l) := by omega
  conv_lhs => rw [hsplit, Finset.sum_range_add]
  have hfirst : ∑ a ∈ Finset.range l, min a l = gamma l := by
    rw [← sum_range_id l]
    apply Finset.sum_congr rfl
    intro a ha
    exact min_eq_left (Nat.le_of_lt (Finset.mem_range.mp ha))
  rw [hfirst]
  congr 1
  simp only [Nat.le_add_right, min_eq_right, Finset.sum_const, Finset.card_range, smul_eq_mul]

theorem lowerColumn_disjoint (w j a c : ℕ) (hac : a ≠ c) :
    Disjoint (lowerColumn w a j) (lowerColumn w c j) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [lowerColumn, box, Finset.mem_product, Finset.mem_Ico] at hx hy
  omega

theorem lowerPool_card {w T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) :
    ((lowerPool w T j).card : ℤ) = gamma T - gamma (T - j + 1) := by
  have hdisj : (↑(Finset.range T) : Set ℕ).PairwiseDisjoint
      (fun a => lowerColumn w a j) := by
    intro a ha c hc hac
    exact lowerColumn_disjoint w j a c hac
  rw [lowerPool, Finset.card_biUnion hdisj, Nat.cast_sum]
  simp_rw [lowerColumn_card w _ j hj]
  rw [← Nat.cast_sum]
  rw [sum_min (by omega : j - 1 ≤ T), Nat.cast_add, Nat.cast_mul]
  have hs := gamma_add (j - 1) (T - j + 1)
  rw [show j - 1 + (T - j + 1) = T by omega] at hs
  have hs' : (gamma T : ℤ) = gamma (j - 1) + gamma (T - j + 1) +
      (j - 1 : ℕ) * (T - j + 1 : ℕ) := by exact_mod_cast hs
  have he : T - (j - 1) = T - j + 1 := by omega
  rw [he]
  nlinarith

theorem suffixColumn_card {w h T j : ℕ} (hjT : j ≤ T) (hh : gamma T ≤ h) :
    ((suffixColumn w h T j).card : ℤ) = h + 1 - j * ((T : ℤ) - j) := by
  rw [suffixColumn, box_card_int (by omega) (by omega)]
  have hs := gamma_add j (T - j)
  rw [show j + (T - j) = T by omega] at hs
  have hs' : (gamma T : ℤ) = gamma j + gamma (T - j) + (j : ℤ) * (T - j : ℕ) := by
    exact_mod_cast hs
  have hcast : ((T - j : ℕ) : ℤ) = (T : ℤ) - j := by omega
  rw [hcast] at hs'
  nlinarith

theorem suffixStrip_card {w h T j : ℕ} (hj : 1 ≤ j) (hw : T ≤ w) :
    ((suffixStrip w h T j).card : ℤ) = ((w : ℤ) - T) * (j - 1) := by
  have hg := gamma_int_succ (j - 1)
  rw [show j - 1 + 1 = j by omega] at hg
  have hpred : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  rw [hpred] at hg
  rw [suffixStrip, box_card_int (by omega) (by omega)]
  rw [show -(gamma (j - 1) : ℤ) - -(gamma j : ℤ) = j - 1 by omega]
  ring

theorem suffixPool_card {w h T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hw : 2 * T ≤ w) (hh : gamma T ≤ h) :
    ((suffixPool w h T j).card : ℤ) = externalDemand w h T j + gamma (j + 1) - 1 := by
  have hd1 : Disjoint (suffixColumn w h T j) (suffixStrip w h T j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    simp only [suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  have hd2 : Disjoint (suffixColumn w h T j ∪ suffixStrip w h T j) (lowerPool w T j) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨a, ha, hy⟩ := Finset.mem_biUnion.mp hy
    have ha' := Finset.mem_range.mp ha
    simp only [Finset.mem_union, suffixColumn, suffixStrip, lowerColumn, box,
      Finset.mem_product, Finset.mem_Ico] at hx hy
    rcases hx with hx | hx <;> omega
  rw [suffixPool, Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1,
    Nat.cast_add, Nat.cast_add, suffixColumn_card hjT hh,
    suffixStrip_card hj (by omega), lowerPool_card hj hjT]
  have hs := gamma_add (j - 1) (T - j + 1)
  rw [show j - 1 + (T - j + 1) = T by omega] at hs
  have hs' : (gamma T : ℤ) = gamma (j - 1) + gamma (T - j + 1) +
      (j - 1 : ℕ) * (T - j + 1 : ℕ) := by exact_mod_cast hs
  have hg := gamma_int_succ (j - 1)
  rw [show j - 1 + 1 = j by omega] at hg
  have hpred : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  have hcast : ((T - j + 1 : ℕ) : ℤ) = (T : ℤ) - j + 1 := by omega
  rw [hpred, hcast] at hs'
  rw [hpred] at hg
  dsimp [externalDemand]
  rw [gamma_int_succ j]
  nlinarith

theorem external_pool_capacity {w h T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hw : 2 * T ≤ w) (hh : gamma T ≤ h) :
    externalDemand w h T j ≤ ((prefixPool w h T j).card : ℤ) ∧
      externalDemand w h T j ≤ ((suffixPool w h T j).card : ℤ) := by
  rw [prefixPool_card hj hjT (by omega), suffixPool_card hj hjT hw hh]
  have hg := gamma_int_mono (show 2 ≤ j + 1 by omega)
  have hg2 : gamma 2 = 1 := by rfl
  rw [hg2] at hg
  omega


def secondPrefixOwners (T j : ℕ) : Finset Lattice :=
  (inverseSet (primaryTwo T) 0 ∩ inverseSet (primaryTwo T) (j - 1)) \ inverseSet (primaryTwo T) j

theorem auxiliaryHeight_ge_gamma (T : ℕ) : gamma T ≤ auxiliaryHeight T := by
  have hg := gamma_quadratic T
  unfold auxiliaryHeight
  by_cases hT : 2 ≤ T
  · have hp : T - 1 + 1 = T := by omega
    have hp2 : T - 2 + 2 = T := by omega
    nlinarith [Nat.zero_le ((T - 1) * (T - 2))]
  · have ht : T = 0 ∨ T = 1 := by omega
    rcases ht with rfl | rfl <;> decide

theorem secondIntersection_boxes {T b : ℕ} (hb : b ≤ T) :
    inverseSet (primaryTwo T) 0 ∩ inverseSet (primaryTwo T) b =
      box (3 * T) ((4 * T : ℤ) - b)
        (3 * gamma T) ((3 * gamma T + auxiliaryHeight T : ℤ) - gamma b) := by
  ext x
  simp only [Finset.mem_inter, mem_inverseSet, primaryTwo, box, translate,
    gamma_zero, Nat.cast_zero, add_zero, Finset.mem_product, Finset.mem_Ico]
  omega

theorem secondIntersection_card {T b : ℕ} (hb : b ≤ T) :
    (((inverseSet (primaryTwo T) 0 ∩ inverseSet (primaryTwo T) b).card) : ℤ) =
      ((T : ℤ) - b) * ((auxiliaryHeight T : ℤ) - gamma b) := by
  have hγ := gamma_int_mono hb
  have hB := auxiliaryHeight_ge_gamma T
  rw [secondIntersection_boxes hb, box_card_int (by omega) (by omega)]
  ring

theorem secondPrefixOwners_card {T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T) :
    ((secondPrefixOwners T j).card : ℤ) =
      (auxiliaryHeight T : ℤ) - gamma j + ((T : ℤ) - j + 1) * (j - 1) := by
  let A := inverseSet (primaryTwo T) 0 ∩ inverseSet (primaryTwo T) (j - 1)
  let B := inverseSet (primaryTwo T) 0 ∩ inverseSet (primaryTwo T) j
  have hsub : B ⊆ A := by
    intro x hx
    simp only [B, A, Finset.mem_inter, mem_inverseSet] at hx ⊢
    exact ⟨hx.1, primaryTwo_between (by omega) (by omega) hx.1 hx.2⟩
  have he : secondPrefixOwners T j = A \ B := by
    ext x
    simp only [secondPrefixOwners, A, B, Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨ha, hn⟩; exact ⟨ha, fun hb => hn hb.2⟩
    · rintro ⟨ha, hn⟩; exact ⟨ha, fun hb => hn ⟨ha.1, hb⟩⟩
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  rw [← he] at hc
  have hc' : ((secondPrefixOwners T j).card : ℤ) + B.card = A.card := by exact_mod_cast hc
  dsimp [A, B] at hc'
  rw [secondIntersection_card hjT, secondIntersection_card (by omega)] at hc'
  have hg := gamma_int_succ (j - 1)
  rw [show j - 1 + 1 = j by omega] at hg
  have hpred : ((j - 1 : ℕ) : ℤ) = (j : ℤ) - 1 := by omega
  rw [hpred] at hc' hg
  nlinarith

theorem net_external_demand {w h T j : ℕ} (hT : 2 ≤ T) (hj : 1 ≤ j) (hjT : j ≤ T)
    (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    ((firstSuffixOwners w h T j).card : ℤ) + (secondPrefixOwners T j).card =
      externalDemand w h T j := by
  rw [firstSuffixOwners_card hj hjT hw hh, secondPrefixOwners_card hj hjT]
  have hg0 : 2 * (gamma T : ℤ) + T = (T : ℤ) * T := by exact_mod_cast gamma_quadratic T
  have hg : 2 * (gamma T : ℤ) = (T : ℤ) * (T - 1) := by nlinarith
  have hB : (auxiliaryHeight T : ℤ) = ((T : ℤ) - 1) ^ 2 + 1 := by
    unfold auxiliaryHeight
    have hp : ((T - 1 : ℕ) : ℤ) = (T : ℤ) - 1 := by omega
    push_cast
    rw [hp]
  rw [hB]
  dsimp [sigma, externalDemand]
  nlinarith

end RigidGHZ.Planar


