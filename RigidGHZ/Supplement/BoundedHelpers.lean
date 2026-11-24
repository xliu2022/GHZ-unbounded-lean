module

public import RigidGHZ.Supplement.ThresholdArithmetic
public import RigidGHZ.Supplement.MatchingRestriction

/-! Transport and restriction of the actual witnesses used in threshold proofs. -/

@[expose] public section

namespace RigidGHZ.Supplement

namespace BoundedRigid

variable {r m d D c : ℕ} {b : ℕ → ℕ}

theorem restrict_pair (h : BoundedRigid r m D (pairBounds D c))
    (hd : d ≤ D) (hr : 1 ≤ r) (hm : 1 ≤ m) :
    BoundedRigid r m d (pairBounds d c) := by
  classical
  letI : Nonempty (Fin r × Fin m) := ⟨⟨⟨0, by omega⟩, ⟨0, by omega⟩⟩⟩
  obtain ⟨H, hU, hP, ⟨R⟩, hD⟩ := h
  obtain ⟨K, hKH, hRK⟩ := R.exists_restriction (d := d) (by simpa using hd)
  apply boundedRigid_of_pair_bound (hU.mono hKH) (hP.mono hKH) hRK
  exact (maxDegree_mono hKH 2).trans (by simpa [pairBounds] using hD 2 (by decide))

theorem forget_bounds (h : BoundedRigid r m d b) :
    BoundedRigid r m d (fun _ => d) := by
  obtain ⟨H, hU, hP, hR, _⟩ := h
  exact ⟨H, hU, hP, hR, fun _ hj => maxDegree_rigid_le hR hj⟩

theorem to_unrestricted (h : BoundedRigid r m d b) :
    BoundedUnrestricted r m d b := by
  classical
  obtain ⟨H, hU, _, hR, hD⟩ := h
  let e : (Fin r × Fin m) ≃ Fin (r * m) := Fintype.equivFinOfCardEq (by simp)
  refine ⟨relabelHypergraph e H, hU.relabel e, hR.relabel e, ?_⟩
  intro j hj
  simpa only [maxDegree_relabel] using hD j hj

/-- A consecutive window of witnesses fills its entire arithmetic progression. -/
theorem stride_window {a stride base : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (hb : 1 ≤ base) (seed : BoundedRigid r (stride * a + 1) d b)
    (initial : ∀ i : Fin a, BoundedRigid r (base + stride * i.val) d b)
    (q : ℕ) : BoundedRigid r (base + stride * q) d b := by
  let i : Fin a := ⟨q % a, Nat.mod_lt _ ha⟩
  have h := (initial i).progression seed hr (by omega) (q / a)
  have he : base + stride * i.val + (stride * a) * (q / a) = base + stride * q := by
    dsimp [i]
    calc
      base + stride * (q % a) + stride * a * (q / a) =
          base + stride * (q % a + a * (q / a)) := by ring
      _ = base + stride * q := by rw [Nat.mod_add_div]
  simpa only [he] using h

end BoundedRigid

namespace BoundedUnrestricted

variable {r m d D : ℕ} {b : ℕ → ℕ}

theorem of_witness {H : Hypergraph (Fin (r * m))}
    (hU : Uniform H r) (hR : IsRigid H d) :
    BoundedUnrestricted r m d (fun _ => d) :=
  ⟨H, hU, hR, fun _ hj => maxDegree_rigid_le hR hj⟩

theorem restrict (h : BoundedUnrestricted r m D b) (hd : d ≤ D)
    (hr : 1 ≤ r) (hm : 1 ≤ m) :
    BoundedUnrestricted r m d (fun _ => d) := by
  classical
  letI : Nonempty (Fin (r * m)) := ⟨⟨0, by positivity⟩⟩
  obtain ⟨H, hU, ⟨R⟩, _⟩ := h
  obtain ⟨K, hKH, hRK⟩ := R.exists_restriction (d := d) (by simpa using hd)
  exact of_witness (hU.mono hKH) hRK

theorem stride_window {a stride base : ℕ} (ha : 0 < a) (hr : 1 ≤ r)
    (hb : 1 ≤ base) (seed : BoundedRigid r (stride * a + 1) d b)
    (initial : ∀ i : Fin a, BoundedUnrestricted r (base + stride * i.val) d b)
    (q : ℕ) : BoundedUnrestricted r (base + stride * q) d b := by
  let i : Fin a := ⟨q % a, Nat.mod_lt _ ha⟩
  have h := (initial i).progression seed hr (by omega) (q / a)
  have he : base + stride * i.val + (stride * a) * (q / a) = base + stride * q := by
    dsimp [i]
    calc
      base + stride * (q % a) + stride * a * (q / a) =
          base + stride * (q % a + a * (q / a)) := by ring
      _ = base + stride * q := by rw [Nat.mod_add_div]
  simpa only [he] using h

end BoundedUnrestricted
end RigidGHZ.Supplement
