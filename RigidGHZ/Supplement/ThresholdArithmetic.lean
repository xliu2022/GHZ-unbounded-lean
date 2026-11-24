module

public import RigidGHZ.Supplement.GraftSemigroup

/-! The finite residue-certificate argument used by the supplementary thresholds. -/

@[expose] public section

namespace RigidGHZ.Supplement

/-- A representative of the same residue cannot exceed a number above the
conductor bound `W-a+1` if all representatives are at most `W`. -/
theorem residue_le_of_threshold {a W s w : ℕ} (ha : 0 < a)
    (hmod : s % a = w % a) (hw : w ≤ W) (hs : W - a + 1 ≤ s) : w ≤ s := by
  by_contra hn
  have hlt : s < w := by omega
  have hsq := Nat.mod_add_div s a
  have hwq := Nat.mod_add_div w a
  have hquot : s / a < w / a := by
    by_contra h
    have hm := Nat.mul_le_mul_left a (show w / a ≤ s / a by omega)
    omega
  have hstep := Nat.mul_le_mul_left a (Nat.succ_le_of_lt hquot)
  simp only [Nat.mul_succ] at hstep
  have hgap : s + a ≤ w := by omega
  omega

/-- Above that bound, the difference is a nonnegative multiple of the step. -/
theorem residue_representation {a W s w : ℕ} (ha : 0 < a)
    (hmod : s % a = w % a) (hw : w ≤ W) (hs : W - a + 1 ≤ s) :
    ∃ q : ℕ, s = w + a * q := by
  have hle := residue_le_of_threshold ha hmod hw hs
  have hquot : w / a ≤ s / a := Nat.div_le_div_right hle
  have hqeq : w / a + (s / a - w / a) = s / a := by omega
  refine ⟨s / a - w / a, ?_⟩
  have hsq := Nat.mod_add_div s a
  have hwq := Nat.mod_add_div w a
  rw [← hqeq, Nat.mul_add] at hsq
  omega

namespace BoundedRigid

variable {r m d a : ℕ} {b : ℕ → ℕ}

/-- One seed of part size `a+1` extends every starting witness along its progression. -/
theorem progression (h : BoundedRigid r m d b) (seed : BoundedRigid r (a + 1) d b)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (q : ℕ) : BoundedRigid r (m + a * q) d b := by
  induction q with
  | zero => simpa using h
  | succ q ih =>
    have hg := ih.graft seed hr (by omega : 1 ≤ m + a * q) (by omega)
    have he : m + a * q + (a + 1) - 1 = m + a * (q + 1) := by
      rw [Nat.mul_succ]
      omega
    simpa only [he] using hg

/-- A list of positive graft increments is a direct certificate of its part size. -/
theorem of_increments (xs : List ℕ) (hne : xs ≠ []) (hr : 1 ≤ r)
    (hs : ∀ x ∈ xs, BoundedRigid r (x + 1) d b) :
    BoundedRigid r (1 + xs.sum) d b := by
  have h := semigroup (xs.map (fun x => x + 1)) (by simpa using hne) hr (by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact ⟨by omega, hs x hx⟩)
  simpa [List.map_map, Function.comp_def] using h

/-- The residue-table proof of Supplementary Theorem S7.2. Every entry is a
list of actual available seed increments; no existence claim is assumed for
any number outside that finite seed list. -/
theorem residue_threshold {W : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (rows : Fin a → List ℕ)
    (hmod : ∀ i, (rows i).sum % a = i.val)
    (hmax : ∀ i, (rows i).sum ≤ W)
    (seed : BoundedRigid r (a + 1) d b)
    (hrows : ∀ i x, x ∈ rows i → BoundedRigid r (x + 1) d b)
    (m : ℕ) (hm : 2 ≤ m) (hthreshold : W - a + 2 ≤ m) :
    BoundedRigid r m d b := by
  let i : Fin a := ⟨(m - 1) % a, Nat.mod_lt _ ha⟩
  have hres : (m - 1) % a = (rows i).sum % a := (hmod i).symm
  obtain ⟨q, hq⟩ := residue_representation ha hres (hmax i)
    (show W - a + 1 ≤ m - 1 by omega)
  let xs := rows i ++ List.replicate q a
  have hsum : xs.sum = m - 1 := by
    simpa [xs, List.sum_append, List.sum_replicate, Nat.mul_comm] using hq.symm
  have hne : xs ≠ [] := by
    intro he
    have hz : xs.sum = 0 := by rw [he]; rfl
    omega
  have hseeds : ∀ x ∈ xs, BoundedRigid r (x + 1) d b := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hrows i x hx
    · have hxa : x = a := (List.mem_replicate.mp hx).2
      simpa only [hxa] using seed
  have h := of_increments xs hne hr hseeds
  have he : 1 + xs.sum = m := by omega
  simpa only [he] using h

end BoundedRigid

namespace BoundedUnrestricted

variable {r m d a : ℕ} {b : ℕ → ℕ}

theorem progression (h : BoundedUnrestricted r m d b) (seed : BoundedRigid r (a + 1) d b)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (q : ℕ) : BoundedUnrestricted r (m + a * q) d b := by
  induction q with
  | zero => simpa using h
  | succ q ih =>
    have hg := ih.graft seed hr (by omega : 1 ≤ m + a * q) (by omega)
    have he : m + a * q + (a + 1) - 1 = m + a * (q + 1) := by
      rw [Nat.mul_succ]
      omega
    simpa only [he] using hg

end BoundedUnrestricted
end RigidGHZ.Supplement
