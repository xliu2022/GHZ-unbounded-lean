module

public import RigidGHZ.Construction.RectanglePatterns
public import Mathlib.Data.Int.Interval
public import Mathlib.Tactic

/-!
# The actual inverse translates of a primary rectangle

Reflection converts the positive-shift rectangles used for counting into the
inverse translates in the construction. All exit patterns are preserved.
-/

@[expose] public section

namespace RigidGHZ.Rectangle

/-- Reflect natural grid coordinates in the upper-right corner of a rectangle. -/
def reflectEmbedding (Y Z : ℤ) (W J : ℕ) : (ℕ × ℕ) ↪ (ℤ × ℤ) where
  toFun x := (Y + W - 1 - x.1, Z + J - 1 - x.2)
  inj' := by
    intro x y h
    have hx := congrArg Prod.fst h
    have hy := congrArg Prod.snd h
    apply Prod.ext <;> dsimp at hx hy <;> omega

/-- The inverse translate by `(b, choose b 2)` of a rectangle with lower-left
corner `(Y,Z)` and side lengths `W,J`. -/
def inverseRectangle (Y Z : ℤ) (W J b : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Ico (Y - b) (Y + W - b)).product
    (Finset.Ico (Z - gamma b) (Z + J - gamma b))

 theorem mem_inverseRectangle_reflect_iff (Y Z : ℤ) (W J b : ℕ) (x : ℕ × ℕ) :
    reflectEmbedding Y Z W J x ∈ inverseRectangle Y Z W J b ↔ x ∈ rectangle W J b := by
  simp only [inverseRectangle, rectangle, reflectEmbedding, Function.Embedding.coeFn_mk,
    Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico]
  omega

 theorem inverseRectangle_eq_map (Y Z : ℤ) (W J b : ℕ) :
    inverseRectangle Y Z W J b = (rectangle W J b).map (reflectEmbedding Y Z W J) := by
  ext x
  constructor
  · intro hx
    have hx' := hx
    simp only [inverseRectangle, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico] at hx'
    have hu : 0 ≤ Y + W - 1 - x.1 := by omega
    have hv : 0 ≤ Z + J - 1 - x.2 := by omega
    let u : ℕ × ℕ := ((Y + W - 1 - x.1).toNat, (Z + J - 1 - x.2).toNat)
    have hreflect : reflectEmbedding Y Z W J u = x := by
      apply Prod.ext
      · dsimp [reflectEmbedding, u]
        rw [Int.toNat_of_nonneg hu]
        omega
      · dsimp [reflectEmbedding, u]
        rw [Int.toNat_of_nonneg hv]
        omega
    apply Finset.mem_map.mpr
    refine ⟨u, ?_, hreflect⟩
    apply (mem_inverseRectangle_reflect_iff Y Z W J b u).mp
    rwa [hreflect]
  · rintro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    exact (mem_inverseRectangle_reflect_iff Y Z W J b u).mpr hu

/-- Direct membership is exactly the original translated-point condition. -/
theorem mem_inverseRectangle_iff (Y Z : ℤ) (W J b : ℕ) (x : ℤ × ℤ) :
    x ∈ inverseRectangle Y Z W J b ↔
      Y ≤ x.1 + b ∧ x.1 + b < Y + W ∧
      Z ≤ x.2 + gamma b ∧ x.2 + gamma b < Z + J := by
  simp only [inverseRectangle, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico]
  omega

def inverseExits (Y Z : ℤ) (W J T : ℕ) (x : ℤ × ℤ) : Finset ℕ :=
  (Finset.range (T + 1)).filter (fun b => x ∈ inverseRectangle Y Z W J b)

 theorem inverseExits_reflect (Y Z : ℤ) (W J T : ℕ) (x : ℕ × ℕ) :
    inverseExits Y Z W J T (reflectEmbedding Y Z W J x) = exits W J T x := by
  ext b
  simp only [inverseExits, exits, Finset.mem_filter, mem_inverseRectangle_reflect_iff]

 theorem inverseExits_between {Y Z : ℤ} {W J T : ℕ} {x : ℤ × ℤ} {a b c : ℕ}
    (ha : a ∈ inverseExits Y Z W J T x) (hc : c ∈ inverseExits Y Z W J T x)
    (hab : a ≤ b) (hbc : b ≤ c) : b ∈ inverseExits Y Z W J T x := by
  have hag := gamma_mono hab
  have hcg := gamma_mono hbc
  simp only [inverseExits, Finset.mem_filter, Finset.mem_range,
    inverseRectangle, Finset.product_eq_sprod, Finset.mem_product, Finset.mem_Ico] at ha hc ⊢
  omega

/-- Union of the actual inverse translates, namely all owners of the rectangle. -/
def inverseOwners (Y Z : ℤ) (W J T : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.range (T + 1)).biUnion (inverseRectangle Y Z W J)

 theorem inverseOwners_eq_map (Y Z : ℤ) (W J T : ℕ) :
    inverseOwners Y Z W J T = (rectangleUnion W J T).map (reflectEmbedding Y Z W J) := by
  ext x
  simp only [inverseOwners, rectangleUnion, Finset.mem_biUnion,
    inverseRectangle_eq_map, Finset.mem_map]
  constructor
  · rintro ⟨b, hb, u, hu, hux⟩
    exact ⟨u, ⟨b, hb, hu⟩, hux⟩
  · rintro ⟨u, ⟨b, hb, hu⟩, hux⟩
    exact ⟨b, hb, u, hu, hux⟩

 theorem inverseOwners_card (Y Z : ℤ) (W J T : ℕ) (hW : 1 ≤ W) (hT : T ≤ J + 1) :
    (inverseOwners Y Z W J T).card = (W + T) * J + (W - 1) * gamma T := by
  rw [inverseOwners_eq_map, Finset.card_map]
  exact rectangleUnion_card W J T hW hT

/-- Reflecting an arbitrary collection of owner patterns preserves its exact count. -/
theorem reflected_patterns_card (Y Z : ℤ) (W J : ℕ) (S : Finset (ℕ × ℕ)) :
    (S.map (reflectEmbedding Y Z W J)).card = S.card := Finset.card_map _

/-- For a row `i`, subtracting its fixed vertical translation gives the actual
three-coordinate tag condition in the primary rectangle. -/
theorem inverse_row_membership (Y Z : ℤ) (W J i b : ℕ) (x : ℤ × ℤ) :
    x ∈ inverseRectangle Y (Z - gamma i) W J b ↔
      Y ≤ x.1 + b ∧ x.1 + b < Y + W ∧
      Z ≤ x.2 + gamma i + gamma b ∧ x.2 + gamma i + gamma b < Z + J := by
  rw [mem_inverseRectangle_iff]
  omega

end RigidGHZ.Rectangle
