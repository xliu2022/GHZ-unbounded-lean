module

public import RigidGHZ.Construction.RectanglePatterns
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic.FinCases

/-!
# External anchors for the rectangular construction

The six pools are represented by injective maps from finite rectangular
index sets.  All interval endpoints and all shifts are integral.
-/

@[expose] public section

namespace RigidGHZ.RectangleAnchors

open RigidGHZ.Rectangle
open scoped Finset

abbrev Lattice := ℤ × ℤ × ℤ

def box (lx ux ly uy lz uz : ℤ) : Finset Lattice :=
  (Finset.Ico lx ux) ×ˢ ((Finset.Ico ly uy) ×ˢ (Finset.Ico lz uz))

def tagBox (A B H T : ℕ) : Finset Lattice :=
  box 0 (A + T) 0 (B + T) 0 (H + 2 * (gamma T : ℤ) + 1)

def holeBox (A B H T : ℕ) : Finset Lattice :=
  box T A T B (2 * (gamma T : ℤ)) H

def projectionEnvelope (A B H : ℕ) : Finset Lattice := box 0 A 0 B 0 (H + 1)

def translate (i b : ℕ) (x : Lattice) : Lattice :=
  (x.1 + i, x.2.1 + b, x.2.2 + (gamma i : ℤ) + (gamma b : ℤ))

def gap (offset width x : ℤ) : ℤ := if x < offset then x - offset else width + x - offset

theorem gap_injective {offset width : ℤ} (hw : 0 ≤ width) :
    Function.Injective (gap offset width) := by
  intro x y h
  unfold gap at h
  split_ifs at h <;> omega

theorem gap_outside {offset width x : ℤ} (hw : 0 ≤ width) :
    gap offset width x < 0 ∨ width ≤ gap offset width x := by
  unfold gap
  split_ifs <;> omega

def fullHorizontal (A i : ℕ) {T B H : ℕ} (x : Fin T × Fin B × Fin H) : Lattice :=
  (gap i A x.1.val, x.2.1.val, x.2.2.val)

def fullVertical (H i : ℕ) {A B T : ℕ} (x : Fin A × Fin B × Fin (gamma T)) : Lattice :=
  (x.1.val, x.2.1.val, gap (gamma i) (H + 1) x.2.2.val)

def prefixHorizontal (B T l : ℕ) {A H : ℕ} (x : Fin A × Fin H) : Lattice :=
  (x.1.val, (B : ℤ) + T - l - 1, x.2.val)

def prefixVertical (H T i l : ℕ) {A B : ℕ} (x : Fin A × Fin B × Fin l) : Lattice :=
  (x.1.val, x.2.1.val,
    (H : ℤ) + 1 + 2 * gamma T - gamma i - gamma (l + 1) + x.2.2.val)

def suffixHorizontal (l : ℕ) {A H : ℕ} (x : Fin A × Fin H) : Lattice :=
  (x.1.val, -(l + 1 : ℤ), x.2.val)

def suffixVertical (i l : ℕ) {A B : ℕ} (x : Fin A × Fin B × Fin l) : Lattice :=
  (x.1.val, x.2.1.val, -(gamma i : ℤ) - gamma (l + 1) + x.2.2.val)

theorem fullHorizontal_injective (A i T B H : ℕ) :
    Function.Injective (@fullHorizontal A i T B H) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    have hg := gap_injective (offset := (i : ℤ)) (Int.natCast_nonneg A)
      (congrArg Prod.fst h)
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · apply Prod.ext
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.1) h
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.2) h
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg

theorem fullVertical_injective (H i A B T : ℕ) :
    Function.Injective (@fullVertical H i A B T) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    have hg := congrArg Prod.fst h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · apply Prod.ext
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.1) h
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg
    · apply Fin.ext
      have hg := gap_injective (offset := (gamma i : ℤ)) (by omega : 0 ≤ (H : ℤ) + 1)
        (congrArg (fun x : Lattice => x.2.2) h)
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg

theorem prefixHorizontal_injective (B T l A H : ℕ) :
    Function.Injective (@prefixHorizontal B T l A H) := by
  intro x y h
  apply Prod.ext <;> apply Fin.ext
  · have hg := congrArg Prod.fst h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · have hg := congrArg (fun x : Lattice => x.2.2) h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg

theorem prefixVertical_injective (H T i l A B : ℕ) :
    Function.Injective (@prefixVertical H T i l A B) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    have hg := congrArg Prod.fst h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · apply Prod.ext
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.1) h
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.2) h
      dsimp [prefixVertical] at hg
      omega

theorem suffixHorizontal_injective (l A H : ℕ) :
    Function.Injective (@suffixHorizontal l A H) := by
  intro x y h
  apply Prod.ext <;> apply Fin.ext
  · have hg := congrArg Prod.fst h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · have hg := congrArg (fun x : Lattice => x.2.2) h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg

theorem suffixVertical_injective (i l A B : ℕ) :
    Function.Injective (@suffixVertical i l A B) := by
  intro x y h
  apply Prod.ext
  · apply Fin.ext
    have hg := congrArg Prod.fst h
    try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
      suffixHorizontal, suffixVertical] at hg
    exact_mod_cast hg
  · apply Prod.ext
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.1) h
      try dsimp only [fullHorizontal, fullVertical, prefixHorizontal, prefixVertical,
        suffixHorizontal, suffixVertical] at hg
      exact_mod_cast hg
    · apply Fin.ext
      have hg := congrArg (fun x : Lattice => x.2.2) h
      dsimp [suffixVertical] at hg
      omega

theorem gamma_cast_mono {a b : ℕ} (h : a ≤ b) : (gamma a : ℤ) ≤ gamma b := by
  exact_mod_cast gamma_mono h

theorem gamma_cast_succ (a : ℕ) : (gamma (a + 1) : ℤ) = gamma a + a := by
  exact_mod_cast gamma_succ a

theorem fullHorizontal_valid {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (x : Fin T × Fin B × Fin H) :
    translate i b (fullHorizontal A i x) ∈ tagBox A B H T \ holeBox A B H T ∧
      fullHorizontal A i x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono hb
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  simp only [translate, fullHorizontal, gap, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  split_ifs <;> omega

theorem fullVertical_valid {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (x : Fin A × Fin B × Fin (gamma T)) :
    translate i b (fullVertical H i x) ∈ tagBox A B H T \ holeBox A B H T ∧
      fullVertical H i x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono hb
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  simp only [translate, fullVertical, gap, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  split_ifs <;> omega

theorem prefixHorizontal_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hl : l < T)
    (hb : b ≤ l) (x : Fin A × Fin H) :
    translate i b (prefixHorizontal B T l x) ∈ tagBox A B H T \ holeBox A B H T ∧
      prefixHorizontal B T l x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono (show b ≤ T by omega)
  have hx := x.1.isLt
  have hz := x.2.isLt
  simp only [translate, prefixHorizontal, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  omega

theorem prefixVertical_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hl : l < T)
    (hb : b ≤ l) (x : Fin A × Fin B × Fin l) :
    translate i b (prefixVertical H T i l x) ∈ tagBox A B H T \ holeBox A B H T ∧
      prefixVertical H T i l x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono hb
  have hgl := gamma_cast_mono (show l + 1 ≤ T by omega)
  have hgam := gamma_cast_succ l
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  simp only [translate, prefixVertical, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  omega

theorem suffixHorizontal_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (hlb : l + 1 ≤ b) (x : Fin A × Fin H) :
    translate i b (suffixHorizontal l x) ∈ tagBox A B H T \ holeBox A B H T ∧
      suffixHorizontal l x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono hb
  have hx := x.1.isLt
  have hz := x.2.isLt
  simp only [translate, suffixHorizontal, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  omega

theorem suffixVertical_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (hlb : l + 1 ≤ b) (x : Fin A × Fin B × Fin l) :
    translate i b (suffixVertical i l x) ∈ tagBox A B H T \ holeBox A B H T ∧
      suffixVertical i l x ∉ projectionEnvelope A B H := by
  have hgi := gamma_cast_mono hi
  have hgb := gamma_cast_mono hb
  have hgl := gamma_cast_mono hlb
  have hgam := gamma_cast_succ l
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  simp only [translate, suffixVertical, tagBox, holeBox, projectionEnvelope, box,
    Finset.mem_sdiff, Finset.mem_product, Finset.mem_Ico]
  omega

def fullHorizontalSet (A B H T i : ℕ) : Finset Lattice :=
  Finset.univ.image (@fullHorizontal A i T B H)
def fullVerticalSet (A B H T i : ℕ) : Finset Lattice :=
  Finset.univ.image (@fullVertical H i A B T)
def prefixHorizontalSet (A B H T l : ℕ) : Finset Lattice :=
  Finset.univ.image (@prefixHorizontal B T l A H)
def prefixVerticalSet (A B H T i l : ℕ) : Finset Lattice :=
  Finset.univ.image (@prefixVertical H T i l A B)
def suffixHorizontalSet (A H l : ℕ) : Finset Lattice :=
  Finset.univ.image (@suffixHorizontal l A H)
def suffixVerticalSet (A B i l : ℕ) : Finset Lattice :=
  Finset.univ.image (@suffixVertical i l A B)

def fullPool (A B H T i : ℕ) : Finset Lattice :=
  fullHorizontalSet A B H T i ∪ fullVerticalSet A B H T i
def prefixPool (A B H T i l : ℕ) : Finset Lattice :=
  prefixHorizontalSet A B H T l ∪ prefixVerticalSet A B H T i l
def suffixPool (A B H i l : ℕ) : Finset Lattice :=
  suffixHorizontalSet A H l ∪ suffixVerticalSet A B i l

theorem fullPieces_disjoint (A B H T i : ℕ) :
    Disjoint (fullHorizontalSet A B H T i) (fullVerticalSet A B H T i) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz'
  have h := congrArg Prod.fst hy
  have hout := gap_outside (offset := (i : ℤ)) (x := (x.1.val : ℤ)) (Int.natCast_nonneg A)
  have hyb := y.1.isLt
  dsimp [fullHorizontal, fullVertical] at h
  omega

theorem prefixPieces_disjoint {A B H T i l : ℕ} (hl : l < T) :
    Disjoint (prefixHorizontalSet A B H T l) (prefixVerticalSet A B H T i l) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz'
  have h := congrArg (fun z : Lattice => z.2.1) hy
  have hyb := y.2.1.isLt
  dsimp [prefixHorizontal, prefixVertical] at h
  omega

theorem suffixPieces_disjoint (A B H i l : ℕ) :
    Disjoint (suffixHorizontalSet A H l) (suffixVerticalSet A B i l) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hz'
  have h := congrArg (fun z : Lattice => z.2.1) hy
  dsimp [suffixHorizontal, suffixVertical] at h
  omega

theorem fullPool_card (A B H T i : ℕ) :
    (fullPool A B H T i).card = T * B * H + A * B * gamma T := by
  rw [fullPool, Finset.card_union_of_disjoint (fullPieces_disjoint A B H T i)]
  rw [fullHorizontalSet, fullVerticalSet,
    Finset.card_image_of_injective _ (fullHorizontal_injective A i T B H),
    Finset.card_image_of_injective _ (fullVertical_injective H i A B T)]
  simp [Nat.mul_assoc]

theorem prefixPool_card {A B H T i l : ℕ} (hl : l < T) :
    (prefixPool A B H T i l).card = A * H + A * B * l := by
  rw [prefixPool, Finset.card_union_of_disjoint (prefixPieces_disjoint hl)]
  rw [prefixHorizontalSet, prefixVerticalSet,
    Finset.card_image_of_injective _ (prefixHorizontal_injective B T l A H),
    Finset.card_image_of_injective _ (prefixVertical_injective H T i l A B)]
  simp [Nat.mul_assoc]

theorem suffixPool_card (A B H i l : ℕ) :
    (suffixPool A B H i l).card = A * H + A * B * l := by
  rw [suffixPool, Finset.card_union_of_disjoint (suffixPieces_disjoint A B H i l)]
  rw [suffixHorizontalSet, suffixVerticalSet,
    Finset.card_image_of_injective _ (suffixHorizontal_injective l A H),
    Finset.card_image_of_injective _ (suffixVertical_injective i l A B)]
  simp [Nat.mul_assoc]

theorem fullPool_valid {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    {z : Lattice} (hz : z ∈ fullPool A B H T i) :
    translate i b z ∈ tagBox A B H T \ holeBox A B H T ∧
      z ∉ projectionEnvelope A B H := by
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact fullHorizontal_valid hi hb x
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact fullVertical_valid hi hb x

theorem prefixPool_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hl : l < T)
    (hb : b ≤ l) {z : Lattice} (hz : z ∈ prefixPool A B H T i l) :
    translate i b z ∈ tagBox A B H T \ holeBox A B H T ∧
      z ∉ projectionEnvelope A B H := by
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact prefixHorizontal_valid hi hl hb x
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact prefixVertical_valid hi hl hb x

theorem suffixPool_valid {A B H T i b l : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (hlb : l + 1 ≤ b) {z : Lattice} (hz : z ∈ suffixPool A B H i l) :
    translate i b z ∈ tagBox A B H T \ holeBox A B H T ∧
      z ∉ projectionEnvelope A B H := by
  rcases Finset.mem_union.mp hz with h | h
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact suffixHorizontal_valid hi hb hlb x
  · obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp h
    exact suffixVertical_valid hi hb hlb x

theorem fullHorizontal_bounds {A B H T i : ℕ} {z : Lattice}
    (hz : z ∈ fullHorizontalSet A B H T i) :
    (z.1 < 0 ∨ (A : ℤ) ≤ z.1) ∧ 0 ≤ z.2.1 ∧ z.2.1 < B ∧
      0 ≤ z.2.2 ∧ z.2.2 < H := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hout := gap_outside (offset := (i : ℤ)) (x := (x.1.val : ℤ)) (Int.natCast_nonneg A)
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  dsimp [fullHorizontal]
  omega

theorem fullVertical_bounds {A B H T i : ℕ} {z : Lattice}
    (hz : z ∈ fullVerticalSet A B H T i) :
    0 ≤ z.1 ∧ z.1 < A ∧ 0 ≤ z.2.1 ∧ z.2.1 < B ∧
      ((-(gamma i : ℤ) ≤ z.2.2 ∧ z.2.2 < 0) ∨
       ((H : ℤ) + 1 ≤ z.2.2 ∧ z.2.2 ≤ H + gamma T - gamma i)) := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  dsimp [fullVertical, gap]
  split_ifs <;> omega

theorem prefixHorizontal_bounds {A B H T l : ℕ} {z : Lattice}
    (hz : z ∈ prefixHorizontalSet A B H T l) :
    0 ≤ z.1 ∧ z.1 < A ∧ z.2.1 = (B : ℤ) + T - l - 1 ∧ 0 ≤ z.2.2 ∧ z.2.2 < H := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hx := x.1.isLt
  have hz := x.2.isLt
  dsimp [prefixHorizontal]
  omega

theorem prefixVertical_bounds {A B H T i l : ℕ} {z : Lattice}
    (hz : z ∈ prefixVerticalSet A B H T i l) :
    0 ≤ z.1 ∧ z.1 < A ∧ 0 ≤ z.2.1 ∧ z.2.1 < B ∧
      (H : ℤ) + 1 + 2 * gamma T - gamma i - gamma (l + 1) ≤ z.2.2 ∧
      z.2.2 ≤ H + 2 * (gamma T : ℤ) - gamma i - gamma l := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  have hγ := gamma_cast_succ l
  dsimp [prefixVertical]
  omega

theorem suffixHorizontal_bounds {A H l : ℕ} {z : Lattice}
    (hz : z ∈ suffixHorizontalSet A H l) :
    0 ≤ z.1 ∧ z.1 < A ∧ z.2.1 = -(l + 1 : ℤ) ∧ 0 ≤ z.2.2 ∧ z.2.2 < H := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hx := x.1.isLt
  have hz := x.2.isLt
  dsimp [suffixHorizontal]
  omega

theorem suffixVertical_bounds {A B i l : ℕ} {z : Lattice}
    (hz : z ∈ suffixVerticalSet A B i l) :
    0 ≤ z.1 ∧ z.1 < A ∧ 0 ≤ z.2.1 ∧ z.2.1 < B ∧
      -(gamma i : ℤ) - gamma (l + 1) ≤ z.2.2 ∧
      z.2.2 ≤ -(gamma i : ℤ) - gamma l - 1 := by
  obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
  have hx := x.1.isLt
  have hy := x.2.1.isLt
  have hz := x.2.2.isLt
  have hγ := gamma_cast_succ l
  dsimp [suffixVertical]
  omega

theorem fullPool_disjoint_prefixPool {A B H T i l : ℕ} (hi : i ≤ T) (hl : l < T) :
    Disjoint (fullPool A B H T i) (prefixPool A B H T i l) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hgi := gamma_cast_mono hi
  have hgl := gamma_cast_mono (show l + 1 ≤ T by omega)
  rcases Finset.mem_union.mp hz with hh | hv <;>
    rcases Finset.mem_union.mp hz' with hh' | hv'
  · have h := fullHorizontal_bounds hh
    have h' := prefixHorizontal_bounds hh'
    omega
  · have h := fullHorizontal_bounds hh
    have h' := prefixVertical_bounds hv'
    omega
  · have h := fullVertical_bounds hv
    have h' := prefixHorizontal_bounds hh'
    omega
  · have h := fullVertical_bounds hv
    have h' := prefixVertical_bounds hv'
    omega

theorem fullPool_disjoint_suffixPool (A B H T i l : ℕ) :
    Disjoint (fullPool A B H T i) (suffixPool A B H i l) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rcases Finset.mem_union.mp hz with hh | hv <;>
    rcases Finset.mem_union.mp hz' with hh' | hv'
  · have h := fullHorizontal_bounds hh
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := fullHorizontal_bounds hh
    have h' := suffixVertical_bounds hv'
    omega
  · have h := fullVertical_bounds hv
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := fullVertical_bounds hv
    have h' := suffixVertical_bounds hv'
    omega

theorem prefixPool_disjoint_suffixPool {A B H T i l j : ℕ} (hi : i ≤ T) (hl : l < T) :
    Disjoint (prefixPool A B H T i l) (suffixPool A B H i j) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  have hgi := gamma_cast_mono hi
  have hgl := gamma_cast_mono (show l + 1 ≤ T by omega)
  rcases Finset.mem_union.mp hz with hh | hv <;>
    rcases Finset.mem_union.mp hz' with hh' | hv'
  · have h := prefixHorizontal_bounds hh
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := prefixHorizontal_bounds hh
    have h' := suffixVertical_bounds hv'
    omega
  · have h := prefixVertical_bounds hv
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := prefixVertical_bounds hv
    have h' := suffixVertical_bounds hv'
    omega

theorem prefixPool_disjoint_prefixPool {A B H T i l j : ℕ}
    (hl : l < T) (hj : j < T) (hlj : l ≠ j) :
    Disjoint (prefixPool A B H T i l) (prefixPool A B H T i j) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rcases Finset.mem_union.mp hz with hh | hv <;>
    rcases Finset.mem_union.mp hz' with hh' | hv'
  · have h := prefixHorizontal_bounds hh
    have h' := prefixHorizontal_bounds hh'
    omega
  · have h := prefixHorizontal_bounds hh
    have h' := prefixVertical_bounds hv'
    omega
  · have h := prefixVertical_bounds hv
    have h' := prefixHorizontal_bounds hh'
    omega
  · have h := prefixVertical_bounds hv
    have h' := prefixVertical_bounds hv'
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · have hg := gamma_cast_mono (show l + 1 ≤ j by omega)
      omega
    · have hg := gamma_cast_mono (show j + 1 ≤ l by omega)
      omega

theorem suffixPool_disjoint_suffixPool {A B H i l j : ℕ} (hlj : l ≠ j) :
    Disjoint (suffixPool A B H i l) (suffixPool A B H i j) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  rcases Finset.mem_union.mp hz with hh | hv <;>
    rcases Finset.mem_union.mp hz' with hh' | hv'
  · have h := suffixHorizontal_bounds hh
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := suffixHorizontal_bounds hh
    have h' := suffixVertical_bounds hv'
    omega
  · have h := suffixVertical_bounds hv
    have h' := suffixHorizontal_bounds hh'
    omega
  · have h := suffixVertical_bounds hv
    have h' := suffixVertical_bounds hv'
    rcases lt_or_gt_of_ne hlj with hlt | hgt
    · have hg := gamma_cast_mono (show l + 1 ≤ j by omega)
      omega
    · have hg := gamma_cast_mono (show j + 1 ≤ l by omega)
      omega

end RigidGHZ.RectangleAnchors
