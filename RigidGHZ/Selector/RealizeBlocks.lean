module

public import RigidGHZ.Selector.ExpandedDoubleComb
public import Mathlib.Logic.Equiv.Fintype

@[expose] public section

namespace RigidGHZ.Selector

open BlockExpansion

/-- A collection of disjoint nonempty finite owner blocks can be put in arbitrary
fixed orders. All remaining vertices become the isolated summand. -/
theorem realize_blocks {V W : Type*} [DecidableEq W]
    (B : V → Finset W) (hdisj : Pairwise (fun v w => Disjoint (B v) (B w)))
    (hpos : ∀ v, (B v).Nonempty) :
    ∃ n : V → ℕ, ∃ e : (Point n ⊕ {w : W // ∀ v, w ∉ B v}) ≃ W,
      (∀ v, n v + 1 = (B v).card) ∧
      (∀ v k, e (Sum.inl (⟨v, k⟩ : Point n)) ∈ B v) ∧
      ∀ z, e (Sum.inr z) = z.val := by
  classical
  let n : V → ℕ := fun v => (B v).card - 1
  have hc : ∀ v, n v + 1 = (B v).card := by
    intro v
    have hp := Finset.card_pos.mpr (hpos v)
    dsimp [n]
    omega
  let ev : ∀ v, Fin (n v + 1) ≃ ↥(B v) := fun v =>
    Fintype.equivOfCardEq (by simpa using hc v)
  let Z := {w : W // ∀ v, w ∉ B v}
  let f : Point n ⊕ Z → W := fun x => match x with
    | Sum.inl ⟨v, k⟩ => (ev v k).val
    | Sum.inr z => z.val
  have hfi : Function.Injective f := by
    intro x y h
    cases x with
    | inl x =>
      rcases x with ⟨v, k⟩
      cases y with
      | inl y =>
        rcases y with ⟨w, l⟩
        have hvw : v = w := by
          by_contra hvw
          apply Finset.disjoint_left.mp (hdisj hvw) (ev v k).property
          change (ev v k).val ∈ B w
          change (ev v k).val = (ev w l).val at h
          rw [h]
          exact (ev w l).property
        subst w
        have hkl : k = l := (ev v).injective (Subtype.ext h)
        subst l
        rfl
      | inr z =>
        change (ev v k).val = z.val at h
        exact (z.property v (h ▸ (ev v k).property)).elim
    | inr z =>
      cases y with
      | inl y =>
        rcases y with ⟨v, k⟩
        change z.val = (ev v k).val at h
        exact (z.property v (h.symm ▸ (ev v k).property)).elim
      | inr z' => exact congrArg Sum.inr (Subtype.ext h)
  have hfs : Function.Surjective f := by
    intro w
    by_cases hw : ∃ v, w ∈ B v
    · obtain ⟨v, hv⟩ := hw
      refine ⟨Sum.inl ⟨v, (ev v).symm ⟨w, hv⟩⟩, ?_⟩
      change ((ev v) ((ev v).symm ⟨w, hv⟩)).val = w
      rw [(ev v).apply_symm_apply]
    · exact ⟨Sum.inr ⟨w, by simpa using hw⟩, rfl⟩
  let e : Point n ⊕ Z ≃ W := Equiv.ofBijective f ⟨hfi, hfs⟩
  refine ⟨n, e, hc, ?_, ?_⟩
  · intro v k
    exact (ev v k).property
  · intro z
    rfl

/-- Exhaustiveness is invariant under any relabeling of the ground set. -/
theorem complete_relabel {V W I : Type*} (e : V ≃ W) (p : I → Equiv.Perm V)
    (hcomplete : ∀ q : Equiv.Perm V, (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (Q : Equiv.Perm W)
    (hQ : ∀ w, ∃ i, Q w = e.permCongr (p i) w) :
    ∃ i, Q = e.permCongr (p i) := by
  let q := e.symm.permCongr Q
  have hq : ∀ a, ∃ i, q a = p i a := by
    intro a
    obtain ⟨i, hi⟩ := hQ (e a)
    refine ⟨i, ?_⟩
    have h := congrArg e.symm hi
    simpa [q] using h
  obtain ⟨i, hi⟩ := hcomplete q hq
  refine ⟨i, ?_⟩
  apply Equiv.ext
  intro w
  have h := congrArg (fun r : Equiv.Perm V => e (r (e.symm w))) hi
  simpa [q] using h

 theorem relabel_moves_iff {V W : Type*} (e : V ≃ W) (p : Equiv.Perm V) (w : W) :
    e.permCongr p w ≠ w ↔ p (e.symm w) ≠ e.symm w := by
  have h : e.permCongr p w = w ↔ p (e.symm w) = e.symm w := by
    rw [Equiv.permCongr_apply]
    exact e.eq_symm_apply.symm
  exact not_congr h

end RigidGHZ.Selector
