module

public import RigidGHZ.Selector.DoubleComb

/-! Delete one vertex on a forced edge, splicing its predecessor to its successor.
The cycle-cover completeness theorem is preserved. -/

@[expose] public section

namespace RigidGHZ.Selector.ForcedContraction

open Equiv Equiv.Perm

variable {V I : Type*} [DecidableEq V]

abbrev Remaining (a : V) := {x : V // x ≠ a}

def contracted (a b : V) (p : Equiv.Perm V) (hp : p a = b) :
    Equiv.Perm (Remaining a) :=
  (swap a b * p).subtypePerm (fun x => by
    have hf : (swap a b * p) a = a := by simp [hp]
    constructor
    · intro hn hx
      apply hn
      rw [hx, hf]
    · intro hn he
      apply hn
      exact (swap a b * p).injective (he.trans hf.symm))

@[simp] theorem contracted_apply (a b : V) (p : Equiv.Perm V) (hp : p a = b)
    (x : Remaining a) : (contracted a b p hp x).val = swap a b (p x.val) := rfl

def expanded (a b : V) (q : Equiv.Perm (Remaining a)) : Equiv.Perm V :=
  swap a b * ofSubtype q

@[simp] theorem expanded_at_removed (a b : V) (q : Equiv.Perm (Remaining a)) :
    expanded a b q a = b := by
  simp [expanded, ofSubtype_apply_of_not_mem]

@[simp] theorem expanded_at_remaining (a b : V) (q : Equiv.Perm (Remaining a))
    (x : Remaining a) : expanded a b q x.val = swap a b (q x).val := by
  simp [expanded]

theorem contracted_expanded (a b : V) (q : Equiv.Perm (Remaining a)) :
    contracted a b (expanded a b q) (expanded_at_removed a b q) = q := by
  ext x
  rw [contracted_apply, expanded_at_remaining, swap_apply_self]

theorem expanded_contracted (a b : V) (p : Equiv.Perm V) (hp : p a = b) :
    expanded a b (contracted a b p hp) = p := by
  ext x
  by_cases hx : x = a
  · subst x
    simp [hp]
  · change expanded a b (contracted a b p hp) (⟨x, hx⟩ : Remaining a).val = p x
    rw [expanded_at_remaining, contracted_apply, swap_apply_self]

/-- A graph's contracted relation removes the forced vertex exactly. In particular,
a loop at the successor is allowed only if the original graph has the corresponding
arc back to the removed vertex. -/
def Arc (A : V → V → Prop) (a b : V) (x y : Remaining a) : Prop :=
  A x.val (swap a b y.val)

theorem contracted_cover (A : V → V → Prop) (a b : V)
    (p : Equiv.Perm V) (hp : p a = b) (hcover : ∀ x, A x (p x)) :
    ∀ x, Arc A a b x (contracted a b p hp x) := by
  intro x
  unfold Arc
  rw [contracted_apply, swap_apply_self]
  exact hcover x.val

/-- Completeness of ordinary cycle covers is invariant under deletion of a common
forced vertex. The input hypothesis is proved for the original double comb. -/
theorem complete (A : V → V → Prop) (a b : V) (hab : A a b)
    (p : I → Equiv.Perm V) (hp : ∀ i, p i a = b)
    (hcomplete : ∀ q : Equiv.Perm V, (∀ x, A x (q x)) → ∃ i, q = p i)
    (q : Equiv.Perm (Remaining a)) (hq : ∀ x, Arc A a b x (q x)) :
    ∃ i, q = contracted a b (p i) (hp i) := by
  have he : ∀ x, A x (expanded a b q x) := by
    intro x
    by_cases hx : x = a
    · subst x
      simpa using hab
    · change A x (expanded a b q (⟨x, hx⟩ : Remaining a).val)
      rw [expanded_at_remaining]
      exact hq ⟨x, hx⟩
  obtain ⟨i, hi⟩ := hcomplete (expanded a b q) he
  refine ⟨i, ?_⟩
  ext x
  have heq := congrArg (fun e : Equiv.Perm V => swap a b (e x.val)) hi
  simpa only [expanded_at_remaining, swap_apply_self, contracted_apply] using heq

theorem complete_of_supported (A : V → V → Prop) (a b : V) (hab : A a b)
    (p : I → Equiv.Perm V) (hp : ∀ i, p i a = b)
    (hcovers : ∀ i x, A x (p i x))
    (hcomplete : ∀ q : Equiv.Perm V, (∀ x, A x (q x)) → ∃ i, q = p i)
    (q : Equiv.Perm (Remaining a))
    (hq : ∀ x, ∃ i, q x = contracted a b (p i) (hp i) x) :
    ∃ i, q = contracted a b (p i) (hp i) := by
  apply complete A a b hab p hp hcomplete q
  intro x
  obtain ⟨i, hi⟩ := hq x
  rw [hi]
  exact contracted_cover A a b (p i) (hp i) (hcovers i) x


/-- A forced edge not lying in a 2-cycle preserves the set of moved remaining vertices. -/
theorem contracted_moves_iff (a b : V) (p : Equiv.Perm V) (hp : p a = b)
    (hno : p b ≠ a) (x : Remaining a) :
    contracted a b p hp x ≠ x ↔ p x.val ≠ x.val := by
  apply not_congr
  constructor
  · intro h
    have he := congrArg Subtype.val h
    rw [contracted_apply] at he
    have hxb : x.val ≠ b := by
      intro hx
      rw [hx] at he
      have hs := congrArg (swap a b) he
      apply hno
      simpa only [swap_apply_self, swap_apply_right] using hs
    have he' := congrArg (swap a b) he
    simpa only [swap_apply_self, swap_apply_of_ne_of_ne x.property hxb] using he'
  · intro h
    apply Subtype.ext
    rw [contracted_apply, h]
    have hxb : x.val ≠ b := by
      intro he
      exact x.property (p.injective (h.trans (he.trans hp.symm)))
    exact swap_apply_of_ne_of_ne x.property hxb

end RigidGHZ.Selector.ForcedContraction

