module

public import RigidGHZ.Partite

/-! A finite row-choice certificate, interpreted as ordinary matching completeness. -/

@[expose] public section

namespace RigidGHZ.Finite

noncomputable def rigidFamily_of_row_certificate
    {I A W : Type*} [Fintype I] [Fintype A] [Fintype W]
    [DecidableEq A] [DecidableEq W]
    (a0 : A) (p : I → A → W → W)
    (hbij : ∀ i a, Function.Bijective (p i a))
    (hroot : ∀ i w, p i a0 w = w)
    (hsep : ∀ i j, i ≠ j → ∀ w, ∃ a, p i a w ≠ p j a w)
    (hcert : ∀ c : W → I,
      (∀ a, Function.Injective (fun w => p (c w) a w)) →
      ∃ i, ∀ w a, p (c w) a w = p i a w) :
    RigidFamily (coordinateHypergraph p) I := by
  classical
  let P : I → A → Equiv.Perm W := fun i a => Equiv.ofBijective (p i a) (hbij i a)
  apply rigidFamily_of_coordinates a0 P
  · intro i
    exact Equiv.ext (hroot i)
  · exact hsep
  · intro q hq0 hq
    choose c hc using hq
    have hinj : ∀ a, Function.Injective (fun w => p (c w) a w) := by
      intro a u v huv
      apply (q a).injective
      exact (hc u a).trans (huv.trans (hc v a).symm)
    obtain ⟨i, hi⟩ := hcert c hinj
    refine ⟨i, funext fun a => Equiv.ext fun w => ?_⟩
    exact (hc w a).trans (hi w a)

end RigidGHZ.Finite
