module

public import RigidGHZ.Construction.PrimaryRectangles

@[expose] public section

namespace RigidGHZ.Rectangle

/-- Inverse of the row-and-exit translation on the lattice. -/
def untranslateEmbedding (i b : ℕ) : Point3 ↪ Point3 where
  toFun z := (z.1 - i, z.2.1 - b, z.2.2 - (gamma i : ℤ) - gamma b)
  inj' := by
    intro x y h
    have hx := congrArg Prod.fst h
    have hy := congrArg (fun z : Point3 => z.2.1) h
    have hz := congrArg (fun z : Point3 => z.2.2) h
    apply Prod.ext
    · dsimp at hx; omega
    · apply Prod.ext <;> dsimp at hy hz <;> omega

@[simp] theorem translate_untranslate (i b : ℕ) (z : Point3) :
    rowTranslate i b (untranslateEmbedding i b z) = z := by
  apply Prod.ext
  · simp [rowTranslate, untranslateEmbedding]
  · apply Prod.ext <;> dsimp [rowTranslate, untranslateEmbedding] <;> omega

@[simp] theorem untranslate_translate (i b : ℕ) (x : Point3) :
    untranslateEmbedding i b (rowTranslate i b x) = x := by
  apply Prod.ext
  · simp [rowTranslate, untranslateEmbedding]
  · apply Prod.ext <;> dsimp [rowTranslate, untranslateEmbedding] <;> omega

/-- The private vertices of route `(i,b)` are exactly the inverse translates of
all private holes, as in the construction. -/
def privateBlock (Z : Finset Point3) (i b : ℕ) : Finset Point3 :=
  Z.map (untranslateEmbedding i b)

@[simp] theorem privateBlock_card (Z : Finset Point3) (i b : ℕ) :
    (privateBlock Z i b).card = Z.card := Finset.card_map _

 theorem mem_privateBlock_iff (Z : Finset Point3) (i b : ℕ) (x : Point3) :
    x ∈ privateBlock Z i b ↔ rowTranslate i b x ∈ Z := by
  constructor
  · intro hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
    simpa using hz
  · intro hx
    exact Finset.mem_map.mpr ⟨rowTranslate i b x, hx, untranslate_translate i b x⟩

/-- Residues recover a bounded row coordinate even when the lattice coordinates
are treated as integers. -/
theorem grid_coordinate_unique {T : ℕ} {p q : ℤ}
    (hp : p % (T + 1 : ℤ) = 0) (hq : q % (T + 1 : ℤ) = 0)
    (i j : Fin (T + 1)) (heq : p - i.val = q - j.val) : p = q ∧ i = j := by
  have hadd : p + j.val = q + i.val := by omega
  have hm := congrArg (fun a : ℤ => a % (T + 1 : ℤ)) hadd
  have hi : (i.val : ℤ) % (T + 1 : ℤ) = i.val :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)
  have hj : (j.val : ℤ) % (T + 1 : ℤ) = j.val :=
    Int.emod_eq_of_lt (by omega) (by exact_mod_cast j.isLt)
  simp only [Int.add_emod, hp, hq, zero_add, hi, hj] at hm
  have hij : i = j := Fin.ext (by exact_mod_cast hm.symm)
  refine ⟨?_, hij⟩
  have hval := congrArg Fin.val hij
  omega

/-- The first two grid residues determine both the row and the exit. -/
theorem privateBlocks_disjoint {T : ℕ} (Z : Finset Point3)
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0) :
    Pairwise (fun ib jc : Fin (T + 1) × Fin (T + 1) =>
      Disjoint (privateBlock Z ib.1.val ib.2.val) (privateBlock Z jc.1.val jc.2.val)) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hne
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨z, hz, hez⟩ := Finset.mem_map.mp hxi
  obtain ⟨w, hw, hew⟩ := Finset.mem_map.mp hxj
  have heq := hez.trans hew.symm
  have hx := congrArg Prod.fst heq
  have hy := congrArg (fun x : Point3 => x.2.1) heq
  have hij := (grid_coordinate_unique (hgrid z hz).1 (hgrid w hw).1 i j hx).2
  have hbc := (grid_coordinate_unique (hgrid z hz).2 (hgrid w hw).2 b c hy).2
  exact hne (Prod.ext hij hbc)

/-- Grid holes in the interior slab have all their route owners in full layers
of the projection box. -/
theorem privateBlock_inside_full_box {A B H T : ℕ} (Z : Finset Point3)
    (hbox : ∀ z ∈ Z, (T : ℤ) ≤ z.1 ∧ z.1 < A ∧ (T : ℤ) ≤ z.2.1 ∧ z.2.1 < B ∧
      2 * (gamma T : ℤ) ≤ z.2.2 ∧ z.2.2 < H)
    (i b : Fin (T + 1)) {x : Point3} (hx : x ∈ privateBlock Z i.val b.val) :
    0 ≤ x.1 ∧ x.1 < A ∧ 0 ≤ x.2.1 ∧ x.2.1 < B ∧ 0 ≤ x.2.2 ∧ x.2.2 < H := by
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
  have hb := hbox z hz
  have hgi := gamma_mono (Nat.le_of_lt_succ i.isLt)
  have hgb := gamma_mono (Nat.le_of_lt_succ b.isLt)
  dsimp [untranslateEmbedding]
  omega

/-- Private holes placed beyond the last primary level have no owners in common
with any primary rectangle. -/
theorem private_primary_disjoint {T P : ℕ} (Z : Finset Point3)
    (hZ : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)
    (r : PrimaryRectangle) (hr : r.plane ≤ P) (i b j : Fin (T + 1)) :
    Disjoint (privateBlock Z i.val b.val) (r.owners T j.val) := by
  apply Finset.disjoint_left.mpr
  intro x hx hp
  obtain ⟨z, hz, rfl⟩ := Finset.mem_map.mp hx
  have hzl := hZ z hz
  have hb := r.owner_bounds (Nat.le_of_lt_succ j.isLt) hp
  dsimp [untranslateEmbedding] at hb
  omega

 theorem privateBlock_nonempty (Z : Finset Point3) (hZ : Z.Nonempty) (i b : ℕ) :
    (privateBlock Z i b).Nonempty := hZ.map

end RigidGHZ.Rectangle
