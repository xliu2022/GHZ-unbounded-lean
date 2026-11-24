module

public import RigidGHZ.Construction.RectangularFactor
public import RigidGHZ.Construction.RectangleLevels

/-! Concrete placement of the four kinds of primary rectangles. -/

@[expose] public section

namespace RigidGHZ.Rectangle

/-- Natural packing data. The numerical calibration is kept separate from these
finite geometric statements. -/
structure PackedLayout (T B H : ℕ) where
  Lh : ℕ
  Lv : ℕ
  nh : ℕ
  nv : ℕ
  nf : ℕ
  ns : ℕ
  uh : ℕ
  uv : ℕ
  L : ℕ
  Lh_pos : 0 < Lh
  Lv_pos : 0 < Lv
  horizontal_fit : 2 * Lh * T ≤ B
  vertical_fit : 2 * Lv * gamma T + gamma T ≤ H
  horizontal_count : nh ≤ uh * Lh
  vertical_count : nv ≤ uv * Lv
  width_margin : T ≤ B
  height_margin : 2 * gamma T ≤ H
  short_fit : L ≤ H - 2 * gamma T

@[simp] theorem PrimaryRectangle.hole_card (r : PrimaryRectangle) :
    r.hole.card = r.width * r.height := by
  simp [PrimaryRectangle.hole, Finset.card_product, Int.card_Ico]

 theorem PrimaryRectangle.hole_subset_owners_zero (r : PrimaryRectangle) (T : ℕ) :
    r.hole ⊆ r.owners T 0 := by
  intro x hx
  apply (r.mem_owners_iff T 0 x).mpr
  refine ⟨0, Nat.zero_le _, ?_⟩
  simpa [rowTranslate, gamma] using hx

namespace PackedLayout

variable {T B H : ℕ} (s : PackedLayout T B H)

abbrev Index := Fin s.nh ⊕ (Fin s.nv ⊕ (Fin s.nf ⊕ Fin s.ns))

def totalLevels : ℕ := s.uh + s.uv + s.nf + s.ns

def level : s.Index → ℕ
  | .inl a => a.val / s.Lh + 1
  | .inr (.inl a) => s.uh + a.val / s.Lv + 1
  | .inr (.inr (.inl a)) => s.uh + s.uv + a.val + 1
  | .inr (.inr (.inr a)) => s.uh + s.uv + s.nf + a.val + 1

def rectangles : s.Index → PrimaryRectangle
  | .inl a => ⟨s.level (.inl a) * (T + 1), (2 * (a.val % s.Lh) + 1) * T,
      2 * gamma T, T, H - 2 * gamma T⟩
  | .inr (.inl a) => ⟨s.level (.inr (.inl a)) * (T + 1), T,
      (2 * (a.val % s.Lv) + 2) * gamma T, B - T, gamma T⟩
  | .inr (.inr (.inl a)) => ⟨s.level (.inr (.inr (.inl a))) * (T + 1), T,
      2 * gamma T, B - T, H - 2 * gamma T⟩
  | .inr (.inr (.inr a)) => ⟨s.level (.inr (.inr (.inr a))) * (T + 1), T,
      2 * gamma T, B - T, s.L⟩

 theorem horizontal_quotient (a : Fin s.nh) : a.val / s.Lh < s.uh :=
  (Nat.div_lt_iff_lt_mul s.Lh_pos).mpr (a.isLt.trans_le s.horizontal_count)

 theorem vertical_quotient (a : Fin s.nv) : a.val / s.Lv < s.uv :=
  (Nat.div_lt_iff_lt_mul s.Lv_pos).mpr (a.isLt.trans_le s.vertical_count)

 theorem level_pos (a : s.Index) : 1 ≤ s.level a := by
  rcases a with a | a | a | a <;> simp only [level] <;> exact Nat.succ_le_succ (Nat.zero_le _)

 theorem level_le (a : s.Index) : s.level a ≤ s.totalLevels := by
  rcases a with a | a | a | a
  · have := s.horizontal_quotient a
    simp only [level, totalLevels]
    omega
  · have := s.vertical_quotient a
    simp only [level, totalLevels]
    omega
  · have := a.isLt
    simp only [level, totalLevels]
    omega
  · have := a.isLt
    simp only [level, totalLevels]
    omega

@[simp] theorem plane_eq (a : s.Index) : (s.rectangles a).plane = s.level a * (T + 1) := by
  rcases a with a | a | a | a <;> rfl

 theorem plane_multiple (a : s.Index) : (s.rectangles a).plane % (T + 1) = 0 := by
  simp

 theorem plane_lower (a : s.Index) : T + 1 ≤ (s.rectangles a).plane := by
  rw [s.plane_eq]
  have := s.level_pos a
  nlinarith

 theorem plane_upper (a : s.Index) : (s.rectangles a).plane ≤ s.totalLevels * (T + 1) := by
  rw [s.plane_eq]
  exact Nat.mul_le_mul_right _ (s.level_le a)

 theorem y_lower (a : s.Index) : T ≤ (s.rectangles a).y := by
  rcases a with a | a | a | a
  · change T ≤ (2 * (a.val % s.Lh) + 1) * T
    exact le_trans (by omega : T ≤ 1 * T) (Nat.mul_le_mul_right T (by omega))
  all_goals simp only [rectangles]; exact le_rfl

 theorem y_upper (a : s.Index) : (s.rectangles a).y + (s.rectangles a).width ≤ B := by
  rcases a with a | a | a | a
  · have hm := Nat.mod_lt a.val s.Lh_pos
    have hf := s.horizontal_fit
    simp only [rectangles]
    nlinarith
  all_goals simp only [rectangles]; have := s.width_margin; omega

 theorem z_lower (a : s.Index) : 2 * gamma T ≤ (s.rectangles a).z := by
  rcases a with a | a | a | a
  · exact le_rfl
  · change 2 * gamma T ≤ (2 * (a.val % s.Lv) + 2) * gamma T
    exact Nat.mul_le_mul_right _ (by omega)
  all_goals exact le_rfl

 theorem z_upper (a : s.Index) : (s.rectangles a).z + (s.rectangles a).height ≤ H := by
  rcases a with a | a | a | a
  · simp only [rectangles]
    exact Nat.add_sub_of_le s.height_margin |>.le
  · have hm := Nat.mod_lt a.val s.Lv_pos
    have hf := s.vertical_fit
    simp only [rectangles]
    nlinarith
  · simp only [rectangles]
    exact Nat.add_sub_of_le s.height_margin |>.le
  · simp only [rectangles]
    have := s.short_fit
    have := s.height_margin
    omega

 theorem separated : Pairwise (fun a b => (s.rectangles a).Separated T (s.rectangles b)) := by
  intro a b hab
  by_cases hp : (s.rectangles a).plane = (s.rectangles b).plane
  · have hl : s.level a = s.level b :=
      Nat.eq_of_mul_eq_mul_right (Nat.succ_pos T) (by simpa only [s.plane_eq] using hp)
    rcases a with a | a | a | a <;> rcases b with b | b | b | b
    · have hne : a.val % s.Lh ≠ b.val % s.Lh := by
        intro hm
        apply hab
        congr 1
        apply Fin.ext
        have ha := Nat.mod_add_div a.val s.Lh
        have hb := Nat.mod_add_div b.val s.Lh
        simp only [level] at hl
        have hq : a.val / s.Lh = b.val / s.Lh := by omega
        rw [hq, hm] at ha
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr (Or.inl (horizontal_owner_gap hlt))
      · exact Or.inr (Or.inr (Or.inl (horizontal_owner_gap hgt)))
    · have := s.horizontal_quotient a
      have := Nat.zero_le (b.val / s.Lv)
      simp only [level] at hl
      omega
    · have := s.horizontal_quotient a
      simp only [level] at hl
      omega
    · have := s.horizontal_quotient a
      simp only [level] at hl
      omega
    · have := s.horizontal_quotient b
      have := Nat.zero_le (a.val / s.Lv)
      simp only [level] at hl
      omega
    · have hne : a.val % s.Lv ≠ b.val % s.Lv := by
        intro hm
        apply hab
        congr 2
        apply Fin.ext
        have ha := Nat.mod_add_div a.val s.Lv
        have hb := Nat.mod_add_div b.val s.Lv
        simp only [level] at hl
        have hq : a.val / s.Lv = b.val / s.Lv := by omega
        rw [hq, hm] at ha
        omega
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · exact Or.inr (Or.inr (Or.inr (Or.inl (vertical_owner_gap hlt))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (vertical_owner_gap hgt))))
    · have := s.vertical_quotient a
      simp only [level] at hl
      omega
    · have := s.vertical_quotient a
      simp only [level] at hl
      omega
    · have := s.horizontal_quotient b
      simp only [level] at hl
      omega
    · have := s.vertical_quotient b
      simp only [level] at hl
      omega
    · apply (hab ?_).elim
      congr 3
      apply Fin.ext
      simp only [level] at hl
      omega
    · have := a.isLt
      simp only [level] at hl
      omega
    · have := s.horizontal_quotient b
      simp only [level] at hl
      omega
    · have := s.vertical_quotient b
      simp only [level] at hl
      omega
    · have := b.isLt
      simp only [level] at hl
      omega
    · apply (hab ?_).elim
      congr 3
      apply Fin.ext
      simp only [level] at hl
      omega
  · exact Or.inl hp

 theorem owners_in_box {A : ℕ} (hA : s.totalLevels * (T + 1) < A)
    (a : s.Index) (i : Fin (T + 1)) {x : Point3}
    (hx : x ∈ (s.rectangles a).owners T i.val) :
    0 ≤ x.1 ∧ x.1 < A ∧ 0 ≤ x.2.1 ∧ x.2.1 < B ∧ 0 ≤ x.2.2 ∧ x.2.2 < H :=
  (s.rectangles a).owners_inside_full_box (Nat.le_of_lt_succ i.isLt)
    (s.plane_lower a) ((s.plane_upper a).trans_lt hA) (s.y_lower a) (s.y_upper a)
    (s.z_lower a) (s.z_upper a) hx

 theorem ownerBlock_in_box {A : ℕ} (hA : s.totalLevels * (T + 1) < A)
    (i : Fin (T + 1)) (p : Pattern T) {x : Point3} (hx : x ∈ ownerBlock s.rectangles i p) :
    0 ≤ x.1 ∧ x.1 < A ∧ 0 ≤ x.2.1 ∧ x.2.1 < B ∧ 0 ≤ x.2.2 ∧ x.2.2 < H := by
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  exact s.owners_in_box hA a i (owner_map_subset s.rectangles a i p hx)

 theorem widths_ge (hB : 2 * T ≤ B) (a : s.Index) : T ≤ (s.rectangles a).width := by
  rcases a with a | a | a | a <;> simp only [rectangles] <;> omega

 theorem heights_ge (hH : 3 * gamma T ≤ H) (hL : s.ns ≠ 0 → gamma T ≤ s.L)
    (a : s.Index) : gamma T ≤ (s.rectangles a).height := by
  rcases a with a | a | a | a
  · simp only [rectangles]; omega
  · exact le_rfl
  · simp only [rectangles]; omega
  · exact hL (by have := a.isLt; omega)

 theorem ownerBlock_nonempty (hT : 1 ≤ T) (hB : 2 * T < B) (hH : 3 * gamma T < H)
    (hnh : 0 < s.nh) (hnf : 0 < s.nf) (i : Fin (T + 1)) (p : Pattern T) :
    (Rectangle.ownerBlock s.rectangles i p).Nonempty := by
  apply Rectangle.ownerBlock_nonempty s.rectangles s.plane_multiple s.separated i p
  cases p with
  | full =>
    refine ⟨Sum.inr (Sum.inr (Sum.inl ⟨0, hnf⟩)), ?_⟩
    apply full_owner_nonempty hT
    · change T < B - T; omega
    · change gamma T < H - 2 * gamma T; omega
  | «prefix» l =>
    refine ⟨Sum.inl ⟨0, hnh⟩, ?_⟩
    exact (proper_owner_nonempty (show T ≤ T from le_rfl)
      (show gamma T < H - 2 * gamma T by omega) l).1
  | «suffix» l =>
    refine ⟨Sum.inl ⟨0, hnh⟩, ?_⟩
    exact (proper_owner_nonempty (show T ≤ T from le_rfl)
      (show gamma T < H - 2 * gamma T by omega) l).2

 theorem holes_disjoint : Pairwise (fun a b => Disjoint (s.rectangles a).hole (s.rectangles b).hole) := by
  intro a b hab
  exact Finset.disjoint_of_subset_left ((s.rectangles a).hole_subset_owners_zero T)
    (Finset.disjoint_of_subset_right ((s.rectangles b).hole_subset_owners_zero T)
      ((s.rectangles a).owners_disjoint (s.rectangles b) (s.plane_multiple a)
        (s.plane_multiple b) (s.separated hab) (0 : Fin (T + 1)) (0 : Fin (T + 1))))

/-- The exact primary area used in the calibrated arithmetic. -/
def area : ℕ := s.nh * T * (H - 2 * gamma T) +
  s.nv * (B - T) * gamma T + s.nf * (B - T) * (H - 2 * gamma T) +
  s.ns * (B - T) * s.L

 theorem holes_card : (primaryHoles s.rectangles).card = s.area := by
  have hd : (↑(Finset.univ : Finset s.Index) : Set s.Index).PairwiseDisjoint
      (fun a => (s.rectangles a).hole) := by
    intro a ha b hb hab
    exact s.holes_disjoint hab
  rw [primaryHoles, Finset.card_biUnion hd]
  simp only [PrimaryRectangle.hole_card]
  simp [Index, Fintype.sum_sum_type, rectangles, area, mul_assoc, add_assoc]

 theorem holes_in_box {A : ℕ} (hA : s.totalLevels * (T + 1) < A) :
    primaryHoles s.rectangles ⊆ RectangleAnchors.holeBox A B H T := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  have hpl := s.plane_lower a
  have hpu := (s.plane_upper a).trans_lt hA
  have hy := s.y_lower a
  have hY := s.y_upper a
  have hz := s.z_lower a
  have hZ := s.z_upper a
  simp only [PrimaryRectangle.hole, Finset.mem_product, Finset.mem_singleton,
    Finset.mem_Ico] at hx
  simp only [RectangleAnchors.holeBox, RectangleAnchors.box, Finset.mem_product,
    Finset.mem_Ico]
  omega

end PackedLayout

end RigidGHZ.Rectangle
