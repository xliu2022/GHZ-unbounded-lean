module

public import RigidGHZ.Construction.RectangleUnion
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Zify

/-!
# Owner patterns in a translated rectangle

The membership times of any point form an interval.  Counts of endpoint
patterns and internal intervals are obtained by finite-set differences.
-/

@[expose] public section

namespace RigidGHZ.Rectangle

theorem rectangle_inter_subset {W J a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c) :
    rectangle W J a ∩ rectangle W J c ⊆ rectangle W J b := by
  intro x hx
  have habg := gamma_mono hab
  have hbcg := gamma_mono hbc
  simp only [Finset.mem_inter, rectangle, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

theorem rectangle_inter_card {W J a b : ℕ} (hab : a ≤ b) :
    (rectangle W J a ∩ rectangle W J b).card =
      (W - (b - a)) * (J - (gamma b - gamma a)) := by
  have hg := gamma_mono hab
  unfold rectangle
  rw [Finset.product_inter_product, Finset.Ico_inter_Ico, Finset.Ico_inter_Ico]
  rw [max_eq_right hab, min_eq_left (Nat.add_le_add_right hab W),
    max_eq_right hg, min_eq_left (Nat.add_le_add_right hg J)]
  simp only [Finset.card_product, Nat.card_Ico]
  congr 1 <;> omega

def exits (W J T : ℕ) (x : ℕ × ℕ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun b => x ∈ rectangle W J b)

theorem exits_between {W J T : ℕ} {x : ℕ × ℕ} {a b c : ℕ}
    (ha : a ∈ exits W J T x) (hc : c ∈ exits W J T x)
    (hab : a ≤ b) (hbc : b ≤ c) : b ∈ exits W J T x := by
  simp only [exits, Finset.mem_filter, Finset.mem_range] at ha hc ⊢
  exact ⟨by omega, rectangle_inter_subset hab hbc (Finset.mem_inter.mpr ⟨ha.2, hc.2⟩)⟩

def prefixOwners (W J l : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle W J 0 ∩ rectangle W J l) \ rectangle W J (l + 1)

def suffixOwners (W J T j : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle W J j ∩ rectangle W J T) \ rectangle W J (j - 1)

def internalStarting (W J T l : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle W J (l + 1) \ rectangle W J l) \ rectangle W J T

def internalEnding (W J l : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle W J l \ rectangle W J (l + 1)) \ rectangle W J 0

def wholeRowOwners (W J T : ℕ) : Finset (ℕ × ℕ) :=
  (rectangle W J 0 ∩ rectangle W J T) ∪
    (rectangleUnion W J T \ (rectangle W J 0 ∪ rectangle W J T))

theorem mem_prefixOwners_iff {W J T l : ℕ} (hl : l < T) (x : ℕ × ℕ) :
    x ∈ prefixOwners W J l ↔ exits W J T x = Finset.range (l + 1) := by
  simp only [prefixOwners, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hx0, hxl⟩, hxn⟩
    ext b
    simp only [exits, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hb, hxb⟩
      by_contra h
      have hn : l + 1 ≤ b := by omega
      exact hxn (rectangle_inter_subset (Nat.zero_le _) hn
        (Finset.mem_inter.mpr ⟨hx0, hxb⟩))
    · intro hb
      exact ⟨by omega, rectangle_inter_subset (Nat.zero_le _) (by omega)
        (Finset.mem_inter.mpr ⟨hx0, hxl⟩)⟩
  · intro he
    have h0 : 0 ∈ exits W J T x := by rw [he]; simp
    have hl' : l ∈ exits W J T x := by rw [he]; simp
    have hn : l + 1 ∉ exits W J T x := by rw [he]; simp
    simp only [exits, Finset.mem_filter, Finset.mem_range] at h0 hl' hn
    exact ⟨⟨h0.2, hl'.2⟩, fun h => hn ⟨by omega, h⟩⟩

theorem prefix_card_balance (W J l : ℕ) :
    (prefixOwners W J l).card +
      (rectangle W J 0 ∩ rectangle W J (l + 1)).card =
      (rectangle W J 0 ∩ rectangle W J l).card := by
  have h := Finset.card_sdiff_add_card_inter
    (rectangle W J 0 ∩ rectangle W J l) (rectangle W J (l + 1))
  have hi : (rectangle W J 0 ∩ rectangle W J l) ∩ rectangle W J (l + 1) =
      rectangle W J 0 ∩ rectangle W J (l + 1) := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · intro h
      exact ⟨⟨h.1, rectangle_inter_subset (Nat.zero_le _) (by omega)
        (Finset.mem_inter.mpr h)⟩, h.2⟩
  simpa only [prefixOwners, hi] using h

theorem rectangle_subset_union {W J T b : ℕ} (hb : b ≤ T) :
    rectangle W J b ⊆ rectangleUnion W J T := by
  intro x hx
  exact Finset.mem_biUnion.mpr ⟨b, Finset.mem_range.mpr (by omega), hx⟩

theorem wholeRow_card_balance (W J T : ℕ) :
    (wholeRowOwners W J T).card + 2 * (W * J) =
      (rectangleUnion W J T).card +
        2 * (rectangle W J 0 ∩ rectangle W J T).card := by
  have hu : rectangle W J 0 ∪ rectangle W J T ⊆ rectangleUnion W J T :=
    Finset.union_subset (rectangle_subset_union (Nat.zero_le T))
      (rectangle_subset_union (le_refl T))
  have hd : Disjoint (rectangle W J 0 ∩ rectangle W J T)
      (rectangleUnion W J T \ (rectangle W J 0 ∪ rectangle W J T)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    exact (Finset.mem_sdiff.mp hx').2
      (Finset.mem_union.mpr (Or.inl (Finset.mem_inter.mp hx).1))
  have hs := Finset.card_sdiff_add_card_eq_card hu
  have hc := Finset.card_union_add_card_inter (rectangle W J 0) (rectangle W J T)
  have hw : (wholeRowOwners W J T).card =
      (rectangle W J 0 ∩ rectangle W J T).card +
      (rectangleUnion W J T \ (rectangle W J 0 ∪ rectangle W J T)).card :=
    Finset.card_union_of_disjoint hd
  rw [rectangle_card, rectangle_card] at hc
  omega

theorem le_gamma_add_one (T : ℕ) : T ≤ gamma T + 1 := by
  cases T with
  | zero => omega
  | succ T => rw [gamma_succ]; omega

theorem gamma_quadratic (T : ℕ) : 2 * gamma T + T = T * T := by
  induction T with
  | zero => simp
  | succ T ih => rw [gamma_succ]; nlinarith

theorem wholeRow_card {W J T : ℕ} (hT : 1 ≤ T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (wholeRowOwners W J T).card =
      (W - T) * (J - gamma T) + (T - 1) * gamma T := by
  have hW1 : 1 ≤ W := by omega
  have hTJ : T ≤ J + 1 := (le_gamma_add_one T).trans (Nat.add_le_add_right hJ 1)
  have h := wholeRow_card_balance W J T
  rw [rectangleUnion_card W J T hW1 hTJ,
    rectangle_inter_card (Nat.zero_le T)] at h
  simp only [Nat.sub_zero, gamma_zero] at h
  zify [hW, hW1, hT, hJ] at h ⊢
  nlinarith [h]

theorem prefixOwners_card {W J T l : ℕ} (hl : l < T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (prefixOwners W J l).card = (J - gamma l) + l * (W - l - 1) := by
  have hlW : l ≤ W := by omega
  have hlnW : l + 1 ≤ W := by omega
  have hglJ : gamma l ≤ J := (gamma_mono (by omega)).trans hJ
  have hglnJ : gamma (l + 1) ≤ J := (gamma_mono (by omega)).trans hJ
  have hWl : 1 ≤ W - l := by omega
  have h := prefix_card_balance W J l
  rw [rectangle_inter_card (Nat.zero_le _), rectangle_inter_card (Nat.zero_le _)] at h
  simp only [Nat.sub_zero, gamma_zero] at h
  rw [gamma_succ] at hglnJ h
  zify [hlW, hlnW, hglJ, hglnJ, hWl] at h ⊢
  nlinarith [h]

theorem suffix_card_balance {W J T l : ℕ} (hl : l < T) :
    (suffixOwners W J T (l + 1)).card +
      (rectangle W J l ∩ rectangle W J T).card =
      (rectangle W J (l + 1) ∩ rectangle W J T).card := by
  have h := Finset.card_sdiff_add_card_inter
    (rectangle W J (l + 1) ∩ rectangle W J T) (rectangle W J l)
  have hi : (rectangle W J (l + 1) ∩ rectangle W J T) ∩ rectangle W J l =
      rectangle W J l ∩ rectangle W J T := by
    ext x
    simp only [Finset.mem_inter]
    constructor
    · exact fun h => ⟨h.2, h.1.2⟩
    · intro h
      exact ⟨⟨rectangle_inter_subset (by omega) (by omega)
        (Finset.mem_inter.mpr h), h.2⟩, h.1⟩
  simpa only [suffixOwners, Nat.add_sub_cancel, hi] using h

theorem internalStarting_card_balance (W J T l : ℕ) :
    (internalStarting W J T l).card + (suffixOwners W J T (l + 1)).card =
      (rectangle W J (l + 1) \ rectangle W J l).card := by
  have h := Finset.card_sdiff_add_card_inter
    (rectangle W J (l + 1) \ rectangle W J l) (rectangle W J T)
  have hi : (rectangle W J (l + 1) \ rectangle W J l) ∩ rectangle W J T =
      suffixOwners W J T (l + 1) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, suffixOwners, Nat.add_sub_cancel]
    tauto
  simpa only [internalStarting, hi] using h

theorem newRectangle_card_balance (W J l : ℕ) :
    (rectangle W J (l + 1) \ rectangle W J l).card +
      (W - 1) * (J - l) = W * J := by
  have h := Finset.card_sdiff_add_card_inter (rectangle W J (l + 1)) (rectangle W J l)
  rw [Finset.inter_comm, consecutive_inter_card, rectangle_card] at h
  exact h

theorem prefix_net_demand {W J T l : ℕ} (hl : l < T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (prefixOwners W J l).card = (internalStarting W J T l).card +
      (J - gamma T + (W - T + 1) * l) := by
  have hT : 1 ≤ T := by omega
  have hW1 : 1 ≤ W := by omega
  have hlT : l ≤ T := by omega
  have hlnT : l + 1 ≤ T := by omega
  have hg : gamma l ≤ gamma T := gamma_mono hlT
  have hgn : gamma (l + 1) ≤ gamma T := gamma_mono hlnT
  have hJl : l ≤ J := by
    have h := le_gamma_add_one T
    omega
  have hTW : T - l ≤ W := by omega
  have hTnW : T - (l + 1) ≤ W := by omega
  have hDgl : gamma T - gamma l ≤ J := by omega
  have hDgln : gamma T - gamma (l + 1) ≤ J := by omega
  have hpl := prefixOwners_card hl hW hJ
  have hs := suffix_card_balance (W := W) (J := J) hl
  rw [rectangle_inter_card hlT, rectangle_inter_card hlnT] at hs
  have hi := internalStarting_card_balance W J T l
  have hn := newRectangle_card_balance W J l
  have hglJ : gamma l ≤ J := hg.trans hJ
  have hlW : l ≤ W := by omega
  have hWl : 1 ≤ W - l := by omega
  zify [hW, hW1, hlT, hlnT, hg, hgn, hJl, hTW, hTnW,
    hDgl, hDgln, hJ, hglJ, hlW, hWl] at hpl hs hi hn ⊢
  have hgamma := gamma_succ l
  zify at hgamma
  nlinarith [hpl, hs, hi, hn, hgamma]

theorem internalEnding_card_balance (W J l : ℕ) :
    (internalEnding W J l).card + (prefixOwners W J l).card =
      (rectangle W J l \ rectangle W J (l + 1)).card := by
  have h := Finset.card_sdiff_add_card_inter
    (rectangle W J l \ rectangle W J (l + 1)) (rectangle W J 0)
  have hi : (rectangle W J l \ rectangle W J (l + 1)) ∩ rectangle W J 0 =
      prefixOwners W J l := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_sdiff, prefixOwners]
    tauto
  simpa only [internalEnding, hi] using h

theorem suffix_net_demand {W J T l : ℕ} (hl : l < T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (suffixOwners W J T (l + 1)).card = (internalEnding W J l).card +
      (J - gamma T + (W - T + 1) * l) := by
  have hp := prefix_net_demand hl hW hJ
  have hi := internalStarting_card_balance W J T l
  have he := internalEnding_card_balance W J l
  have hsame : (rectangle W J l \ rectangle W J (l + 1)).card =
      (rectangle W J (l + 1) \ rectangle W J l).card := by
    apply Finset.card_sdiff_eq_card_sdiff_iff.mpr
    simp
  omega

theorem internalStarting_card {W J T l : ℕ} (hl : l < T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (internalStarting W J T l).card =
      gamma T - gamma (l + 1) + l * (T - l - 1) := by
  have hp := prefixOwners_card hl hW hJ
  have hn := prefix_net_demand hl hW hJ
  have hglD : gamma l ≤ gamma T := gamma_mono (by omega)
  have hglnD : gamma (l + 1) ≤ gamma T := gamma_mono (by omega)
  have hglJ := hglD.trans hJ
  have hlW : l ≤ W := by omega
  have hWl : 1 ≤ W - l := by omega
  have hlT : l ≤ T := by omega
  have hTl : 1 ≤ T - l := by omega
  zify [hW, hJ, hglJ, hglnD, hlW, hWl, hlT, hTl] at hp hn ⊢
  have hgamma := gamma_succ l
  zify at hgamma
  nlinarith [hp, hn, hgamma]

/-- All three counts in Lemma A.2, including the two net demands. -/
theorem rectangle_owner_counts {W J T : ℕ} (hT : 1 ≤ T) (hW : T ≤ W)
    (hJ : gamma T ≤ J) :
    (∀ l < T,
      (prefixOwners W J l).card = (internalStarting W J T l).card +
        (J - gamma T + (W - T + 1) * l) ∧
      (suffixOwners W J T (l + 1)).card = (internalEnding W J l).card +
        (J - gamma T + (W - T + 1) * l)) ∧
    (wholeRowOwners W J T).card = (W - T) * (J - gamma T) + (T - 1) * gamma T ∧
    (rectangleUnion W J T).card = (W + T) * J + (W - 1) * gamma T := by
  refine ⟨fun l hl => ⟨prefix_net_demand hl hW hJ, suffix_net_demand hl hW hJ⟩,
    wholeRow_card hT hW hJ, rectangleUnion_card W J T (by omega) ?_⟩
  have h := le_gamma_add_one T
  omega

end RigidGHZ.Rectangle
