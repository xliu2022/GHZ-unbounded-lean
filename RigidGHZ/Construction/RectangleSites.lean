module

public import RigidGHZ.Construction.PackedRectangles

/-! Finite source layers and the separated private-hole grid. -/

@[expose] public section

namespace RigidGHZ.Rectangle

open RectangleAnchors
open scoped Finset

/-- The completely filled source layers below the optional top layer. -/
def fullSourceBox (A B H : ℕ) : Finset Point3 := box 0 A 0 B 0 H

def sourceTopLayer (A B H : ℕ) : Finset Point3 :=
  Finset.Ico (0 : ℤ) A ×ˢ (Finset.Ico (0 : ℤ) B ×ˢ {(H : ℤ)})

@[simp] theorem fullSourceBox_card (A B H : ℕ) :
    (fullSourceBox A B H).card = A * B * H := by
  simp [fullSourceBox, box, Finset.card_product, Int.card_Ico, mul_assoc]

@[simp] theorem sourceTopLayer_card (A B H : ℕ) :
    (sourceTopLayer A B H).card = A * B := by
  simp [sourceTopLayer, Finset.card_product, Int.card_Ico]

 theorem fullSourceBox_disjoint_top (A B H : ℕ) :
    Disjoint (fullSourceBox A B H) (sourceTopLayer A B H) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [fullSourceBox, sourceTopLayer, box, Finset.mem_product, Finset.mem_Ico,
    Finset.mem_singleton] at hx hy
  omega

 theorem source_with_remainder {A B H ρ : ℕ} (hρ : ρ ≤ A * B) :
    ∃ X : Finset Point3, fullSourceBox A B H ⊆ X ∧
      X ⊆ projectionEnvelope A B H ∧ X.card = A * B * H + ρ := by
  obtain ⟨Q, hQ, hQcard⟩ := Finset.exists_subset_card_eq
    (show ρ ≤ (sourceTopLayer A B H).card by simpa using hρ)
  refine ⟨fullSourceBox A B H ∪ Q, Finset.subset_union_left, ?_, ?_⟩
  · intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · simp only [fullSourceBox, box, Finset.mem_product, Finset.mem_Ico] at hx
      simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
      omega
    · have hx := hQ hx
      simp only [sourceTopLayer, Finset.mem_product, Finset.mem_Ico, Finset.mem_singleton] at hx
      simp only [projectionEnvelope, box, Finset.mem_product, Finset.mem_Ico]
      omega
  · rw [Finset.card_union_of_disjoint ((fullSourceBox_disjoint_top A B H).mono_right hQ),
      fullSourceBox_card, hQcard]

/-- Coordinates of the private grid, with the two horizontal coordinates on
multiples of `T+1`. -/
def privateGridEmbedding (T : ℕ) : (ℕ × ℕ × ℕ) ↪ Point3 where
  toFun p := ((p.1 * (T + 1) : ℕ), (p.2.1 * (T + 1) : ℕ), (p.2.2 : ℤ))
  inj' := by
    intro p q hpq
    have hx := congrArg Prod.fst hpq
    have hy := congrArg (fun x : Point3 => x.2.1) hpq
    have hz := congrArg (fun x : Point3 => x.2.2) hpq
    dsimp at hx hy hz
    apply Prod.ext
    · apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos T)
      exact_mod_cast hx
    · apply Prod.ext
      · apply Nat.eq_of_mul_eq_mul_right (Nat.succ_pos T)
        exact_mod_cast hy
      · exact_mod_cast hz

def privateGrid (T H U Px Py : ℕ) : Finset Point3 :=
  ((Finset.Ioc U Px) ×ˢ ((Finset.Icc 1 Py) ×ˢ (Finset.Ico (2 * gamma T) H))).map
    (privateGridEmbedding T)

@[simp] theorem privateGrid_card (T H U Px Py : ℕ) :
    (privateGrid T H U Px Py).card = (Px - U) * Py * (H - 2 * gamma T) := by
  simp [privateGrid, Finset.card_product, mul_assoc]

 theorem privateGrid_multiple {T H U Px Py : ℕ} {z : Point3}
    (hz : z ∈ privateGrid T H U Px Py) :
    z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
  simp [privateGridEmbedding]

 theorem privateGrid_after {T H U Px Py : ℕ} {z : Point3}
    (hz : z ∈ privateGrid T H U Px Py) :
    (U * (T + 1) : ℕ) + (T : ℤ) + 1 ≤ z.1 := by
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
  simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_Ico] at hp
  have hmul : (U + 1) * (T + 1) ≤ p.1 * (T + 1) :=
    Nat.mul_le_mul_right _ (by omega)
  dsimp [privateGridEmbedding]
  push_cast
  exact_mod_cast (show U * (T + 1) + T + 1 ≤ p.1 * (T + 1) by nlinarith)

 theorem privateGrid_inside {A B H T U Px Py : ℕ}
    (hx : Px * (T + 1) < A) (hy : Py * (T + 1) < B) :
    privateGrid T H U Px Py ⊆ holeBox A B H T := by
  intro z hz
  obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hz
  simp only [Finset.mem_product, Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_Ico] at hp
  have hpX := Nat.mul_le_mul_right (T + 1) hp.1.2
  have hpY := Nat.mul_le_mul_right (T + 1) hp.2.1.2
  have hpX0 : T ≤ p.1 * (T + 1) := by nlinarith [hp.1.1]
  have hpY0 : T ≤ p.2.1 * (T + 1) := by nlinarith [hp.2.1.1]
  simp only [holeBox, box, Finset.mem_product, Finset.mem_Ico, privateGridEmbedding,
    Function.Embedding.coeFn_mk, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  constructor
  · constructor <;> exact_mod_cast (by omega : _)
  · constructor
    · constructor <;> exact_mod_cast (by omega : _)
    · constructor <;> exact_mod_cast (by omega : _)

 theorem private_holes_exist {A B H T U Px Py R : ℕ}
    (hx : Px * (T + 1) < A) (hy : Py * (T + 1) < B)
    (hR : R ≤ (Px - U) * Py * (H - 2 * gamma T)) :
    ∃ Z : Finset Point3, Z.card = R ∧ Z ⊆ holeBox A B H T ∧
      (∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0) ∧
      ∀ z ∈ Z, (U * (T + 1) : ℕ) + (T : ℤ) + 1 ≤ z.1 := by
  obtain ⟨Z, hZ, hc⟩ := Finset.exists_subset_card_eq
    (show R ≤ (privateGrid T H U Px Py).card by simpa using hR)
  refine ⟨Z, hc, hZ.trans (privateGrid_inside hx hy), ?_, ?_⟩
  · intro z hz
    exact privateGrid_multiple (hZ hz)
  · intro z hz
    exact privateGrid_after (hZ hz)

@[simp] theorem tagBox_card (A B H T : ℕ) :
    (tagBox A B H T).card = (A + T) * (B + T) * (H + 2 * gamma T + 1) := by
  simp only [tagBox, box, Finset.card_product, Int.card_Ico, sub_zero,
    ← Nat.cast_add, ← Nat.cast_mul, Int.toNat_natCast, mul_assoc]
  rw [show (H : ℤ) + 2 * gamma T + 1 = ((H + 2 * gamma T + 1 : ℕ) : ℤ) by push_cast; rfl,
    Int.toNat_natCast]

 theorem holeBox_subset_tagBox (A B H T : ℕ) : holeBox A B H T ⊆ tagBox A B H T := by
  intro x hx
  simp only [holeBox, tagBox, box, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

 theorem privateBlock_subset_fullSource {A B H T : ℕ} (Z : Finset Point3)
    (hZ : Z ⊆ holeBox A B H T) (i b : Fin (T + 1)) :
    privateBlock Z i.val b.val ⊆ fullSourceBox A B H := by
  intro x hx
  have hcoords : ∀ z ∈ Z, (T : ℤ) ≤ z.1 ∧ z.1 < A ∧ (T : ℤ) ≤ z.2.1 ∧ z.2.1 < B ∧
      2 * (gamma T : ℤ) ≤ z.2.2 ∧ z.2.2 < H := by
    intro z hz
    have hz := hZ hz
    simp only [holeBox, box, Finset.mem_product, Finset.mem_Ico] at hz
    exact ⟨hz.1.1, hz.1.2, hz.2.1.1, hz.2.1.2, hz.2.2.1, hz.2.2.2⟩
  have hb := privateBlock_inside_full_box Z hcoords i b hx
  simp only [fullSourceBox, box, Finset.mem_product, Finset.mem_Ico]
  tauto

end RigidGHZ.Rectangle
