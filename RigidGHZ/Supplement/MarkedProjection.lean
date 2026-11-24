module

public import RigidGHZ.Supplement.CyclicLiftData

/-! A slice projection is bijective once its marked multiplicities obey the
paper's bounds and its coordinate sum agrees with the full residue system. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m : ℕ} [NeZero m]

 theorem finEquiv_eq_natCast (a : Fin m) : ZMod.finEquiv m a = (a.val : ZMod m) := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change a = (a.val : ZMod (n + 1))
    exact (ZMod.natCast_zmod_val (n := n + 1) a).symm

/-- A fiber-count form of finite reindexing, valid before the map is known
bijective. -/
 theorem sum_mul_fiber_count {X Y R : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    [CommSemiring R] (f : X → Y) (g : Y → R) :
    ∑ y, g y * ((Finset.univ.filter (fun x => f x = y)).card : R) = ∑ x, g (f x) := by
  classical
  simpa only [Finset.sum_const, nsmul_eq_mul, mul_comm] using
    Finset.sum_fiberwise' (Finset.univ : Finset X) f g

/-- The marked-coordinate lemma applied to the first projection of a slice.
The hypotheses are local fiber bounds and a modular sum, not bijectivity. -/
 theorem marked_projection_bijective {S : Finset (ZMod m)} (C : Marking S)
    (f : ZMod m → ZMod m)
    (houtside : ∀ a, (ZMod.finEquiv m).symm a ∉ C.marked →
      (Finset.univ.filter (fun b => f b = a)).card = 1)
    (hmarked : ∀ a, (ZMod.finEquiv m).symm a ∈ C.marked →
      (Finset.univ.filter (fun b => f b = a)).card ≤ 2)
    (hsum : ∑ b, f b = ∑ a : ZMod m, a) : Function.Bijective f := by
  classical
  let c : ZMod m → ℕ := fun a => (Finset.univ.filter (fun b => f b = a)).card
  let n : Fin m → ℕ := fun a => c (ZMod.finEquiv m a)
  have hmass : ∑ a, n a = m := by
    calc
      _ = ∑ a, c a := Equiv.sum_comp (ZMod.finEquiv m).toEquiv c
      _ = m := by
        dsimp [c]
        simpa using Finset.sum_card_fiberwise_eq_card_filter Finset.univ Finset.univ f
  have hweight : ∑ a : Fin m, (a.val : ZMod m) * (n a : ZMod m) = ∑ b, f b := by
    simp_rw [← finEquiv_eq_natCast]
    dsimp [n]
    exact (Equiv.sum_comp (ZMod.finEquiv m).toEquiv (fun a => a * (c a : ZMod m))).trans
      (sum_mul_fiber_count f (fun a => a))
  have hplain : ∑ a : Fin m, (a.val : ZMod m) = ∑ a : ZMod m, a := by
    simp_rw [← finEquiv_eq_natCast]
    exact Equiv.sum_comp (ZMod.finEquiv m).toEquiv (fun a => a)
  have hn : ∀ a, n a = 1 := by
    apply Marked.recovery C.marked n C.sum_lt C.superincreasing
    · intro a ha
      apply houtside
      simpa using ha
    · intro a ha
      apply hmarked
      simpa using ha
    · exact hmass
    · apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ m).mp
      push_cast
      simp_rw [mul_sub, mul_one]
      rw [Finset.sum_sub_distrib, hweight, hplain, hsum, sub_self]
  have hc : ∀ a, c a = 1 := by
    intro a
    simpa [n] using hn ((ZMod.finEquiv m).symm a)
  apply Finite.surjective_iff_bijective.mp
  intro a
  have ha := Finset.card_eq_one.mp (hc a)
  obtain ⟨b, hb⟩ := ha
  have hmem : b ∈ Finset.univ.filter (fun b => f b = a) := by rw [hb]; simp
  exact ⟨b, (Finset.mem_filter.mp hmem).2⟩

end RigidGHZ.Supplement.Affine
