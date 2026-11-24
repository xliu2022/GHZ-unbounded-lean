module

public import RigidGHZ.Construction.PlanarGeometry

/-! Primary planar holes, their inverse owners, and interval geometry. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

/-- The L-shaped first primary hole set. -/
def primaryOne (w h T : ℕ) : Finset Lattice :=
  box T (2 * T) (gamma T) h ∪ box (2 * T) w (gamma T) (2 * gamma T)

/-- The second primary rectangle. -/
def primaryTwo (T : ℕ) : Finset Lattice :=
  box (3 * T) (4 * T) (3 * gamma T) (3 * gamma T + auxiliaryHeight T)

def translationEquiv (b : ℕ) : Lattice ≃ Lattice where
  toFun := translate b
  invFun x := (x.1 - b, x.2 - gamma b)
  left_inv x := by cases x; simp [translate]
  right_inv x := by cases x; simp [translate]

def inverseSet (Z : Finset Lattice) (b : ℕ) : Finset Lattice :=
  Z.map (translationEquiv b).symm.toEmbedding

@[simp] theorem mem_inverseSet {Z : Finset Lattice} {b : ℕ} {x : Lattice} :
    x ∈ inverseSet Z b ↔ translate b x ∈ Z := by
  simp [inverseSet, translationEquiv]

@[simp] theorem inverseSet_card (Z : Finset Lattice) (b : ℕ) :
    (inverseSet Z b).card = Z.card := Finset.card_map _

def ownerUnion (Z : Finset Lattice) (T : ℕ) : Finset Lattice :=
  (Finset.range (T + 1)).biUnion (inverseSet Z)

theorem primaryOne_inverse_envelope {w h T b : ℕ}
    (hb : b ≤ T) (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h)
    {x : Lattice} (hx : translate b x ∈ primaryOne w h T) :
    x ∈ box 0 w 0 h ∧ (x.1 < (2 * T : ℤ) ∨ x.2 < (2 * gamma T : ℤ)) := by
  have hg := gamma_int_mono hb
  simp only [primaryOne, box, translate, Finset.mem_union, Finset.mem_product,
    Finset.mem_Ico] at hx ⊢
  rcases hx with hx | hx <;> omega

theorem primaryTwo_inverse_envelope {w h T b : ℕ}
    (hb : b ≤ T) (hw : 4 * T ≤ w) (hh : 3 * gamma T + auxiliaryHeight T ≤ h)
    {x : Lattice} (hx : translate b x ∈ primaryTwo T) :
    x ∈ box 0 w 0 h ∧
      (2 * T : ℤ) ≤ x.1 ∧ x.1 < (4 * T : ℤ) ∧
      (2 * gamma T : ℤ) ≤ x.2 ∧ x.2 < (3 * gamma T + auxiliaryHeight T : ℤ) := by
  have hg := gamma_int_mono hb
  simp only [primaryTwo, box, translate, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

theorem primary_owner_disjoint {w h T b c : ℕ}
    (hb : b ≤ T) (hc : c ≤ T) (hw : 4 * T ≤ w)
    (hh : 3 * gamma T + auxiliaryHeight T ≤ h) :
    Disjoint (inverseSet (primaryOne w h T) b) (inverseSet (primaryTwo T) c) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hx' := primaryOne_inverse_envelope hb (by omega) (by omega) (mem_inverseSet.mp hx)
  have hy' := primaryTwo_inverse_envelope hc hw hh (mem_inverseSet.mp hy)
  omega

/-- The removed-tag exits of the L-shaped hole form an interval. -/
theorem primaryOne_between {w h T a b c : ℕ}
    (hab : a ≤ b) (hbc : b ≤ c) (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h)
    {x : Lattice} (ha : translate a x ∈ primaryOne w h T)
    (hc : translate c x ∈ primaryOne w h T) : translate b x ∈ primaryOne w h T := by
  have hag := gamma_int_mono hab
  have hcg := gamma_int_mono hbc
  simp only [primaryOne, box, translate, Finset.mem_union, Finset.mem_product,
    Finset.mem_Ico] at ha hc ⊢
  rcases ha with ha | ha <;> rcases hc with hc | hc <;>
    by_cases hx : x.1 + (b : ℤ) < 2 * T
  all_goals omega

/-- The interval is proper: no point is removed by both endpoint exits. -/
theorem primaryOne_proper (w h T : ℕ) {x : Lattice}
    (h0 : translate 0 x ∈ primaryOne w h T) : translate T x ∉ primaryOne w h T := by
  simp only [primaryOne, box, translate, gamma_zero, Nat.cast_zero, add_zero,
    Finset.mem_union, Finset.mem_product, Finset.mem_Ico] at h0 ⊢
  omega

theorem primaryTwo_between {T a b c : ℕ} (hab : a ≤ b) (hbc : b ≤ c)
    {x : Lattice} (ha : translate a x ∈ primaryTwo T)
    (hc : translate c x ∈ primaryTwo T) : translate b x ∈ primaryTwo T := by
  have hag := gamma_int_mono hab
  have hcg := gamma_int_mono hbc
  simp only [primaryTwo, box, translate, Finset.mem_product, Finset.mem_Ico] at ha hc ⊢
  omega

theorem primaryTwo_proper (T : ℕ) {x : Lattice}
    (h0 : translate 0 x ∈ primaryTwo T) : translate T x ∉ primaryTwo T := by
  simp only [primaryTwo, box, translate, gamma_zero, Nat.cast_zero, add_zero,
    Finset.mem_product, Finset.mem_Ico] at h0 ⊢
  omega

/-- The two simple strips containing all first-hole owners. -/
def firstOwnerEnvelope (w h T : ℕ) : Finset Lattice :=
  box 0 (2 * T) 0 h ∪ box (2 * T) w 0 (2 * gamma T)

/-- The rectangle containing all second-hole owners. -/
def secondOwnerEnvelope (T : ℕ) : Finset Lattice :=
  box (2 * T) (4 * T) (2 * gamma T) (3 * gamma T + auxiliaryHeight T)

theorem primaryOne_owners_subset {w h T : ℕ} (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    ownerUnion (primaryOne w h T) T ⊆ firstOwnerEnvelope w h T := by
  intro x hx
  obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
  have hmem := primaryOne_inverse_envelope (by simpa using Finset.mem_range.mp hb) hw hh
    (mem_inverseSet.mp hx)
  simp only [box, firstOwnerEnvelope, Finset.mem_union, Finset.mem_product, Finset.mem_Ico] at hmem ⊢
  omega

theorem primaryTwo_owners_subset {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 3 * gamma T + auxiliaryHeight T ≤ h) :
    ownerUnion (primaryTwo T) T ⊆ secondOwnerEnvelope T := by
  intro x hx
  obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.mp hx
  have hmem := primaryTwo_inverse_envelope (by simpa using Finset.mem_range.mp hb) hw hh
    (mem_inverseSet.mp hx)
  simp only [secondOwnerEnvelope, box, Finset.mem_product, Finset.mem_Ico]
  omega

/-- Actual suffix owners of the L-shaped primary holes. -/
def firstSuffixOwners (w h T j : ℕ) : Finset Lattice :=
  (inverseSet (primaryOne w h T) j ∩ inverseSet (primaryOne w h T) T) \ inverseSet (primaryOne w h T) (j - 1)

/-- The entry geometry giving the paper's `sigma_j`. -/
theorem firstSuffixOwners_boxes {w h T j : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    firstSuffixOwners w h T j =
      box ((T : ℤ) - j) ((T : ℤ) - j + 1)
        ((gamma T : ℤ) - gamma j) ((h : ℤ) - gamma T) ∪
      box ((T : ℤ) - j + 1) ((w : ℤ) - T)
        ((gamma T : ℤ) - gamma j) ((gamma T : ℤ) - gamma (j - 1)) := by
  have hgj := gamma_int_mono hjT
  have hgjp := gamma_int_mono (show j - 1 ≤ j by omega)
  ext x
  simp only [firstSuffixOwners, Finset.mem_sdiff, Finset.mem_inter, mem_inverseSet,
    primaryOne, box, translate, Finset.mem_union, Finset.mem_product, Finset.mem_Ico]
  omega

end RigidGHZ.Planar
