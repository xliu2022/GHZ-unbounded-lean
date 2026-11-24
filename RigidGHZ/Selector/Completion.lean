module

public import RigidGHZ.Selector.Hypergraph
public import Mathlib.Logic.Equiv.Fintype

/-!
# Completing a partial tag assignment

The geometric constructions prescribe translated anchors on loops and shared
arcs.  Every remaining arc is private to one cover.  This file proves that
injective partial assignments into a tag set of the correct size extend to
complete assignments, and that the private assignments define a single
anchor function on projected arcs.
-/

@[expose] public section

namespace RigidGHZ.Selector

variable {I W E : Type*} [Fintype W] [AddCommGroup E]

theorem complete_translated_tagging
    (p : I → Equiv.Perm W) (tags : W ↪ E) (v : I → E)
    (Shared : W → W → Prop) (givenAnchor : W → W → E)
    (hvalid : ∀ i a, Shared a (p i a) →
      ∃ t : W, tags t = givenAnchor a (p i a) + v i)
    (hinj : ∀ i a b, Shared a (p i a) → Shared b (p i b) →
      givenAnchor a (p i a) = givenAnchor b (p i b) → a = b)
    (hprivate : ∀ i j a, ¬ Shared a (p i a) → p i a = p j a → i = j) :
    ∃ (c : I → Equiv.Perm W) (anchor : W → W → E),
      (∀ a b, Shared a b → anchor a b = givenAnchor a b) ∧
      ∀ i a, tags (c i a) = anchor a (p i a) + v i := by
  classical
  have hex : ∀ i : I, ∃ c : Equiv.Perm W, ∀ a : W,
      Shared a (p i a) → tags (c a) = givenAnchor a (p i a) + v i := by
    intro i
    let S := {a : W // Shared a (p i a)}
    have hf : ∀ a : S, ∃ t : W, tags t = givenAnchor a (p i a) + v i :=
      fun a => hvalid i a a.property
    choose f hf using hf
    have hfi : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply hinj i a b a.property b.property
      have h := congrArg tags hab
      rw [hf a, hf b] at h
      exact add_right_cancel h
    obtain ⟨c, hc⟩ := Equiv.Perm.exists_extending_pair
      (fun a : S => (a : W)) f Subtype.val_injective hfi
    refine ⟨c, fun a ha => ?_⟩
    rw [hc ⟨a, ha⟩]
    exact hf ⟨a, ha⟩
  choose c hc using hex
  let anchor : W → W → E := fun a b =>
    if Shared a b then givenAnchor a b
    else if h : ∃ i, p i a = b then tags (c h.choose a) - v h.choose else 0
  refine ⟨c, anchor, ?_, ?_⟩
  · intro a b hab
    simp only [anchor, if_pos hab]
  · intro i a
    by_cases ha : Shared a (p i a)
    · simpa only [anchor, if_pos ha] using hc i a ha
    · have hex : ∃ j, p j a = p i a := ⟨i, rfl⟩
      have hi : hex.choose = i :=
        (hprivate i hex.choose a ha hex.choose_spec.symm).symm
      simp only [anchor, if_neg ha, dif_pos hex, hi, sub_add_cancel]

variable [Fintype I] [DecidableEq W] [Module ℝ E]

/-- Filling the private arcs completes the exposed-translation selector. -/
theorem complete_exposed_selector
    (p : I → Equiv.Perm W) (tags : W ↪ E) (v : I → E)
    (Shared : W → W → Prop) (givenAnchor : W → W → E)
    (hvalid : ∀ i a, Shared a (p i a) →
      ∃ t : W, tags t = givenAnchor a (p i a) + v i)
    (hinj : ∀ i a b, Shared a (p i a) → Shared b (p i b) →
      givenAnchor a (p i a) = givenAnchor b (p i b) → a = b)
    (hprivate : ∀ i j a, ¬ Shared a (p i a) → p i a = p j a → i = j)
    (L : I → E →ₗ[ℝ] ℝ) (hexposed : ExposedTranslations v L)
    (covers_complete : ∀ q : Equiv.Perm W,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧ Nonempty (RigidFamily H I) := by
  obtain ⟨c, anchor, _, htag⟩ := complete_translated_tagging p tags v Shared givenAnchor
    hvalid hinj hprivate
  exact ⟨selectorHypergraph p c, selectorHypergraph_uniform p c,
    selectorHypergraph_balanced p c,
    ⟨exposed_selector_rigidFamily p c tags anchor v L htag hexposed covers_complete⟩⟩

end RigidGHZ.Selector
