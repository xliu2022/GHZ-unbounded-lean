module

public import RigidGHZ.Selector.BlockExpansion

@[expose] public section

namespace RigidGHZ.Selector

/-- Adding isolated vertices, on which all prescribed permutations are the identity,
preserves exhaustiveness of the prescribed cycle covers. -/
theorem complete_with_isolated {W Z I : Type*} [Fintype W]
    (p : I → Equiv.Perm W)
    (hcomplete : ∀ q : Equiv.Perm W, (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (Q : Equiv.Perm (W ⊕ Z))
    (hQ : ∀ x, ∃ i, Q x = Equiv.sumCongr (p i) (Equiv.refl Z) x) :
    ∃ i, Q = Equiv.sumCongr (p i) (Equiv.refl Z) := by
  classical
  have hf : ∀ a : W, ∃ b : W, Q (Sum.inl a) = Sum.inl b := by
    intro a
    obtain ⟨i, hi⟩ := hQ (Sum.inl a)
    exact ⟨p i a, hi⟩
  choose f hf using hf
  have hfi : Function.Injective f := by
    intro a b hab
    exact Sum.inl.inj (Q.injective ((hf a).trans ((congrArg Sum.inl hab).trans (hf b).symm)))
  let q : Equiv.Perm W := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi)
  have hq : ∀ a, ∃ i, q a = p i a := by
    intro a
    obtain ⟨i, hi⟩ := hQ (Sum.inl a)
    refine ⟨i, ?_⟩
    exact Sum.inl.inj ((hf a).symm.trans hi)
  obtain ⟨i, hi⟩ := hcomplete q hq
  refine ⟨i, ?_⟩
  apply Equiv.ext
  intro x
  cases x with
  | inl a =>
    change Q (Sum.inl a) = Sum.inl (p i a)
    rw [hf]
    exact congrArg Sum.inl (show f a = p i a from congrArg (fun e : Equiv.Perm W => e a) hi)
  | inr z =>
    obtain ⟨j, hj⟩ := hQ (Sum.inr z)
    exact hj

namespace DoubleComb

open Vertex BlockExpansion

variable {R : Type*} {T : ℕ} (n : Vertex R T → ℕ)

/-- The expanded route has arbitrary positive full-row, suffix, prefix and private blocks. -/
noncomputable def expandedPerm (i : R) (b : Fin (T + 1)) : Equiv.Perm (Point n) :=
  lift n (routePerm i b)

 theorem expandedPerm_cover (i : R) (b : Fin (T + 1)) :
    ∀ x, BlockExpansion.Arc n DoubleComb.Arc x (expandedPerm n i b x) :=
  lift_cover n DoubleComb.Arc (routePerm i b) (routePerm_cover i b)

 theorem expanded_cover_complete [Fintype R] [DecidableEq R]
    (Q : Equiv.Perm (Point n))
    (hQ : ∀ x, BlockExpansion.Arc n DoubleComb.Arc x (Q x)) :
    ∃ i : R, ∃ b : Fin (T + 1), Q = expandedPerm n i b := by
  obtain ⟨i, b, hi⟩ := cover_complete (compress Q hQ) (compress_cover Q hQ)
  refine ⟨i, b, ?_⟩
  rw [← lift_compress Q hQ, hi]
  rfl

 theorem expanded_selector_complete [Fintype R] [DecidableEq R]
    (Q : Equiv.Perm (Point n))
    (hQ : ∀ x, ∃ ib : R × Fin (T + 1), Q x = expandedPerm n ib.1 ib.2 x) :
    ∃ ib : R × Fin (T + 1), Q = expandedPerm n ib.1 ib.2 := by
  have hc : ∀ x, BlockExpansion.Arc n DoubleComb.Arc x (Q x) := by
    intro x
    obtain ⟨⟨i, b⟩, h⟩ := hQ x
    rw [h]
    exact expandedPerm_cover n i b x
  obtain ⟨i, b, hi⟩ := expanded_cover_complete n Q hc
  exact ⟨(i, b), hi⟩

 theorem expandedPerm_moves_iff (i : R) (b : Fin (T + 1)) (x : Point n) :
    expandedPerm n i b x ≠ x ↔ OnRoute i b x.1 :=
  (lift_moves_iff n (routePerm i b) x).trans (routePerm_moves_iff i b x.1)

 theorem expandedPerm_injective :
    Function.Injective (fun ib : R × Fin (T + 1) => expandedPerm n ib.1 ib.2) :=
  (lift_injective n).comp routePerm_injective

/-- Private-chain vertices are precisely the branch blocks. -/
def IsPrivate : Vertex R T → Prop
  | branch _ _ => True
  | _ => False

/-- Shared projected arcs are loops and the non-private portions of the comb. -/
def Shared (x y : Point n) : Prop :=
  x = y ∨ (¬ IsPrivate x.1 ∧ ¬ IsPrivate y.1)

 theorem private_vertex_determines {i j : R} {b c : Fin (T + 1)} (x : Point n)
    (hx : IsPrivate x.1)
    (hi : expandedPerm n i b x ≠ x) (hj : expandedPerm n j c x ≠ x) :
    (i, b) = (j, c) := by
  have hri := (expandedPerm_moves_iff n i b x).mp hi
  have hrj := (expandedPerm_moves_iff n j c x).mp hj
  rcases x with ⟨v, k⟩
  cases v with
  | hub => exact hx.elim
  | upper r a => exact hx.elim
  | lower r a => exact hx.elim
  | branch r a =>
    exact Prod.ext (hri.1.symm.trans hrj.1) (hri.2.symm.trans hrj.2)

/-- Every remaining projected arc belongs to exactly one route, including both
arcs adjacent to a private block and all of its internal arcs. -/
theorem expanded_private_unique (ib jc : R × Fin (T + 1)) (x : Point n)
    (hprivate : ¬ Shared n x (expandedPerm n ib.1 ib.2 x))
    (heq : expandedPerm n ib.1 ib.2 x = expandedPerm n jc.1 jc.2 x) : ib = jc := by
  classical
  have hmove : expandedPerm n ib.1 ib.2 x ≠ x := fun h => hprivate (Or.inl h.symm)
  have hmove' : expandedPerm n jc.1 jc.2 x ≠ x := heq ▸ hmove
  by_cases hx : IsPrivate x.1
  · exact private_vertex_determines n x hx hmove hmove'
  · have hy : IsPrivate (expandedPerm n ib.1 ib.2 x).1 := by
      by_contra h
      exact hprivate (Or.inr ⟨hx, h⟩)
    apply private_vertex_determines n (expandedPerm n ib.1 ib.2 x) hy
    · exact moved_of_predecessor (expandedPerm n ib.1 ib.2) rfl (Ne.symm hmove)
    · exact moved_of_predecessor (expandedPerm n jc.1 jc.2) heq.symm (Ne.symm hmove)

/-- Add any finite set of isolated vertices to the expanded comb. -/
noncomputable def withIsolated {Z : Type*} (ib : R × Fin (T + 1)) :
    Equiv.Perm (Point n ⊕ Z) :=
  Equiv.sumCongr (expandedPerm n ib.1 ib.2) (Equiv.refl Z)

 theorem withIsolated_complete {Z : Type*} [Fintype R] [DecidableEq R]
    (Q : Equiv.Perm (Point n ⊕ Z))
    (hQ : ∀ x, ∃ ib : R × Fin (T + 1), Q x = withIsolated n ib x) :
    ∃ ib : R × Fin (T + 1), Q = withIsolated n ib :=
  complete_with_isolated (fun ib : R × Fin (T + 1) => expandedPerm n ib.1 ib.2)
    (expanded_selector_complete n) Q hQ

/-- Isolated loops remain shared. -/
def SharedWithIsolated {Z : Type*} : (Point n ⊕ Z) → (Point n ⊕ Z) → Prop
  | Sum.inl x, Sum.inl y => Shared n x y
  | Sum.inr _, Sum.inr _ => True
  | _, _ => False

 theorem withIsolated_private_unique {Z : Type*}
    (ib jc : R × Fin (T + 1)) (x : Point n ⊕ Z)
    (hp : ¬ SharedWithIsolated n x (withIsolated n ib x))
    (heq : withIsolated n ib x = withIsolated n jc x) : ib = jc := by
  cases x with
  | inl x => exact expanded_private_unique n ib jc x hp (Sum.inl.inj heq)
  | inr z => exact (hp trivial).elim

end DoubleComb
end RigidGHZ.Selector
