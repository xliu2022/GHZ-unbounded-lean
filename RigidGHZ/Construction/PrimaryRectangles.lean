module

public import RigidGHZ.Construction.InverseRectangles
public import RigidGHZ.Construction.OwnerPatterns

@[expose] public section

namespace RigidGHZ.Rectangle

open scoped Finset

abbrev Point3 := ℤ × ℤ × ℤ

structure PrimaryRectangle where
  plane : ℕ
  y : ℕ
  z : ℕ
  width : ℕ
  height : ℕ

/-- The actual rectangular hole in its primary plane. -/
def PrimaryRectangle.hole (r : PrimaryRectangle) : Finset Point3 :=
  {(r.plane : ℤ)} ×ˢ ((Finset.Ico (r.y : ℤ) (r.y + r.width)) ×ˢ
    (Finset.Ico (r.z : ℤ) (r.z + r.height)))

def rowTranslate (i b : ℕ) (x : Point3) : Point3 :=
  (x.1 + i, x.2.1 + b, x.2.2 + (gamma i : ℤ) + gamma b)

/-- Reflect a positive-shift owner and place it in the unique row plane. -/
def PrimaryRectangle.ownerEmbedding (r : PrimaryRectangle) (i : ℕ) : (ℕ × ℕ) ↪ Point3 where
  toFun u := ((r.plane : ℤ) - i,
    reflectEmbedding r.y ((r.z : ℤ) - gamma i) r.width r.height u)
  inj' := by
    intro u v h
    exact (reflectEmbedding r.y ((r.z : ℤ) - gamma i) r.width r.height).injective
      (congrArg Prod.snd h)

/-- All actual owners of one primary rectangle in one row. -/
def PrimaryRectangle.owners (r : PrimaryRectangle) (T i : ℕ) : Finset Point3 :=
  (rectangleUnion r.width r.height T).map (r.ownerEmbedding i)

 theorem PrimaryRectangle.mem_hole_translate_iff (r : PrimaryRectangle) (i b : ℕ)
    (x : Point3) : rowTranslate i b x ∈ r.hole ↔
      x.1 = (r.plane : ℤ) - i ∧
      x.2 ∈ inverseRectangle r.y ((r.z : ℤ) - gamma i) r.width r.height b := by
  simp only [PrimaryRectangle.hole, rowTranslate, Finset.mem_product,
    Finset.mem_singleton, Finset.mem_Ico, inverse_row_membership]
  omega

/-- This set is exactly the paper's definition of ownership by some exit. -/
theorem PrimaryRectangle.mem_owners_iff (r : PrimaryRectangle) (T i : ℕ) (x : Point3) :
    x ∈ r.owners T i ↔ ∃ b ≤ T, rowTranslate i b x ∈ r.hole := by
  constructor
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨b, hb, hub⟩ := Finset.mem_biUnion.mp hu
    refine ⟨b, by have := Finset.mem_range.mp hb; omega, ?_⟩
    rw [r.mem_hole_translate_iff]
    refine ⟨rfl, ?_⟩
    exact (mem_inverseRectangle_reflect_iff r.y ((r.z : ℤ) - gamma i)
      r.width r.height b u).mpr hub
  · rintro ⟨b, hb, hx⟩
    obtain ⟨hxfirst, hxpair⟩ := (r.mem_hole_translate_iff i b x).mp hx
    rw [inverseRectangle_eq_map] at hxpair
    obtain ⟨u, hu, hueq⟩ := Finset.mem_map.mp hxpair
    apply Finset.mem_map.mpr
    refine ⟨u, Finset.mem_biUnion.mpr ⟨b, Finset.mem_range.mpr (by omega), hu⟩, ?_⟩
    exact Prod.ext hxfirst.symm hueq

 theorem PrimaryRectangle.owner_bounds (r : PrimaryRectangle) {T i : ℕ}
    (hi : i ≤ T) {x : Point3} (hx : x ∈ r.owners T i) :
    x.1 = (r.plane : ℤ) - i ∧
      (r.y : ℤ) - T ≤ x.2.1 ∧ x.2.1 < (r.y : ℤ) + r.width ∧
      (r.z : ℤ) - gamma i - gamma T ≤ x.2.2 ∧
      x.2.2 < (r.z : ℤ) + r.height - gamma i := by
  obtain ⟨b, hb, hxb⟩ := (r.mem_owners_iff T i x).mp hx
  obtain ⟨hfirst, hpair⟩ := (r.mem_hole_translate_iff i b x).mp hxb
  rw [inverse_row_membership] at hpair
  have hg := gamma_mono hb
  have hgi := gamma_mono hi
  refine ⟨hfirst, ?_⟩
  omega

/-- Owners stay in the full layers of the projection box. -/
theorem PrimaryRectangle.owners_inside_full_box (r : PrimaryRectangle)
    {A B H T i : ℕ} (hi : i ≤ T) (hplane : T + 1 ≤ r.plane)
    (hplaneA : r.plane < A) (hy : T ≤ r.y) (hyB : r.y + r.width ≤ B)
    (hz : 2 * gamma T ≤ r.z) (hzH : r.z + r.height ≤ H)
    {x : Point3} (hx : x ∈ r.owners T i) :
    0 ≤ x.1 ∧ x.1 < A ∧ 0 ≤ x.2.1 ∧ x.2.1 < B ∧ 0 ≤ x.2.2 ∧ x.2.2 < H := by
  have hb := r.owner_bounds hi hx
  have hg := gamma_mono hi
  omega

/-- The first coordinate simultaneously identifies the primary level and row. -/
theorem primary_plane_row_unique {T p q : ℕ} (hp : p % (T + 1) = 0)
    (hq : q % (T + 1) = 0) (i j : Fin (T + 1))
    (heq : (p : ℤ) - i.val = (q : ℤ) - j.val) : p = q ∧ i = j := by
  have hadd : p + j.val = q + i.val := by omega
  have hm := congrArg (fun a : ℕ => a % (T + 1)) hadd
  simp only [Nat.add_mod, hp, hq, zero_add,
    Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hm
  have hij : i = j := Fin.ext hm.symm
  refine ⟨?_, hij⟩
  have hv := congrArg Fin.val hij
  omega

/-- Different levels, horizontal gaps of `T`, or vertical gaps of `gamma T`
ensure disjoint ownership. This is exactly the unused-block separation in the
horizontal and vertical primary levels. -/
def PrimaryRectangle.Separated (T : ℕ) (r s : PrimaryRectangle) : Prop :=
  r.plane ≠ s.plane ∨ r.y + r.width + T ≤ s.y ∨ s.y + s.width + T ≤ r.y ∨
    r.z + r.height + gamma T ≤ s.z ∨ s.z + s.height + gamma T ≤ r.z

 theorem PrimaryRectangle.owners_disjoint (r s : PrimaryRectangle) {T : ℕ}
    (hr : r.plane % (T + 1) = 0) (hs : s.plane % (T + 1) = 0)
    (hsep : r.Separated T s) (i j : Fin (T + 1)) :
    Disjoint (r.owners T i.val) (s.owners T j.val) := by
  apply Finset.disjoint_left.mpr
  intro x hxr hxs
  have hb := r.owner_bounds (Nat.le_of_lt_succ i.isLt) hxr
  have hc := s.owner_bounds (Nat.le_of_lt_succ j.isLt) hxs
  obtain ⟨hplane, hij⟩ := primary_plane_row_unique hr hs i j (hb.1.symm.trans hc.1)
  subst j
  rcases hsep with h | h | h | h | h
  · exact h hplane
  all_goals omega

 theorem PrimaryRectangle.rows_disjoint (r : PrimaryRectangle) {T : ℕ}
    (hr : r.plane % (T + 1) = 0) :
    Pairwise (fun i j : Fin (T + 1) => Disjoint (r.owners T i.val) (r.owners T j.val)) := by
  intro i j hij
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  have hi := r.owner_bounds (Nat.le_of_lt_succ i.isLt) hxi
  have hj := r.owner_bounds (Nat.le_of_lt_succ j.isLt) hxj
  exact hij (primary_plane_row_unique hr hr i j (hi.1.symm.trans hj.1)).2

 theorem horizontal_owner_gap {T a b : ℕ} (hab : a < b) :
    (2 * a + 1) * T + T + T ≤ (2 * b + 1) * T := by
  nlinarith

 theorem vertical_owner_gap {T a b : ℕ} (hab : a < b) :
    (2 * a + 2) * gamma T + gamma T + gamma T ≤ (2 * b + 2) * gamma T := by
  nlinarith

/-- The true three-coordinate owner counts are exactly the positive-shift counts. -/
theorem PrimaryRectangle.owners_card (r : PrimaryRectangle) (T i : ℕ)
    (hW : 1 ≤ r.width) (hT : T ≤ r.height + 1) :
    (r.owners T i).card = (r.width + T) * r.height + (r.width - 1) * gamma T := by
  rw [PrimaryRectangle.owners, Finset.card_map]
  exact rectangleUnion_card r.width r.height T hW hT

end RigidGHZ.Rectangle
