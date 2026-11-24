module

public import RigidGHZ.Supplement.Periodic.Height
public import Mathlib.Data.Fintype.Vector
public import Mathlib.LinearAlgebra.Matrix.Trace

/-! A finite directed multigraph with labeled transitions: matrix powers count
paths and traces count cyclic words, with every transition multiplicity retained. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.WeightedWalks

variable {S C : Type*} [Fintype S] [Fintype C] [DecidableEq S]
  (source target : C → S)

 def Chain (s t : S) : List C → Prop
  | [] => s = t
  | c :: cs => source c = s ∧ Chain (target c) t cs

 abbrev Path (n : ℕ) (s t : S) :=
  {v : List.Vector C n // Chain source target s t v.toList}

 abbrev Arc (s t : S) := {c : C // source c = s ∧ target c = t}

noncomputable instance (n : ℕ) (s t : S) : Fintype (Path source target n s t) :=
  Fintype.ofFinite _

noncomputable instance (s t : S) : Fintype (Arc source target s t) :=
  Fintype.ofFinite _

noncomputable def matrix : Matrix S S ℕ := fun s t => Fintype.card (Arc source target s t)

 theorem chain_head_tail {n : ℕ} {s t : S} (v : List.Vector C (n + 1)) :
    Chain source target s t v.toList ↔ source v.head = s ∧
      Chain source target (target v.head) t v.tail.toList := by
  conv_lhs => rw [← List.Vector.cons_head_tail v]
  rfl

noncomputable def pathSuccEquiv (n : ℕ) (s t : S) :
    Path source target (n + 1) s t ≃
      (u : S) × (Arc source target s u × Path source target n u t) where
  toFun p := ⟨target p.1.head,
    ⟨⟨p.1.head, (chain_head_tail source target p.1).mp p.2 |>.1, rfl⟩,
      ⟨p.1.tail, (chain_head_tail source target p.1).mp p.2 |>.2⟩⟩⟩
  invFun p := ⟨List.Vector.cons p.2.1.1 p.2.2.1, by
    simp only [List.Vector.toList_cons, Chain]
    exact ⟨p.2.1.2.1, by simpa only [p.2.1.2.2] using p.2.2.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    exact List.Vector.cons_head_tail p.1
  right_inv p := by
    rcases p with ⟨u, ⟨⟨c, hc, ht⟩, ⟨v, hv⟩⟩⟩
    subst u
    apply Sigma.ext rfl
    apply heq_of_eq
    apply Prod.ext
    · apply Subtype.ext
      exact List.Vector.head_cons c v
    · apply Subtype.ext
      exact List.Vector.tail_cons c v

 theorem path_zero_card (s t : S) : Fintype.card (Path source target 0 s t) =
    if s = t then 1 else 0 := by
  classical
  by_cases hst : s = t
  · subst t
    have hsub : Subsingleton (Path source target 0 s s) :=
      ⟨fun p q => Subtype.ext (Subsingleton.elim p.1 q.1)⟩
    letI := hsub
    letI : Unique (Path source target 0 s s) :=
      ⟨⟨List.Vector.nil, rfl⟩, fun p => Subsingleton.elim _ _⟩
    simp only [if_pos rfl]
    exact Fintype.card_unique
  · have hempty : IsEmpty (Path source target 0 s t) := ⟨by
      rintro ⟨v, hv⟩
      rw [List.Vector.toList_empty] at hv
      exact hst hv⟩
    letI := hempty
    simp [hst]

 theorem path_card (n : ℕ) (s t : S) :
    Fintype.card (Path source target n s t) = (matrix source target ^ n) s t := by
  classical
  induction n generalizing s t with
  | zero => simp only [pow_zero, Matrix.one_apply, path_zero_card]
  | succ n ih =>
    rw [Fintype.card_congr (pathSuccEquiv source target n s t), Fintype.card_sigma]
    simp only [Fintype.card_prod, ih]
    rw [pow_succ', Matrix.mul_apply]
    rfl

 theorem chain_ofFn (n : ℕ) (f : Fin (n + 1) → C) (s t : S) :
    Chain source target s t (List.ofFn f) ↔
      source (f 0) = s ∧ target (f (Fin.last n)) = t ∧
      ∀ i : Fin n, target (f i.castSucc) = source (f i.succ) := by
  induction n generalizing s with
  | zero => simp [List.ofFn_succ, Chain]
  | succ n ih =>
    rw [List.ofFn_succ, Chain, ih]
    simp only [Fin.forall_fin_succ]
    constructor
    · rintro ⟨hs, hnext, ht, hrest⟩
      exact ⟨hs, ht, hnext.symm, hrest⟩
    · rintro ⟨hs, ht, hnext, hrest⟩
      exact ⟨hs, hnext.symm, ht, hrest⟩

 abbrev ClosedWords (q : ℕ) :=
  {f : Fin q → C // ∀ j, target (f j) = source (f (finRotate q j))}

noncomputable instance (q : ℕ) : Fintype (ClosedWords source target q) := Fintype.ofFinite _

noncomputable def closedWordEquiv (n : ℕ) :
    ClosedWords source target (n + 1) ≃ (s : S) × Path source target (n + 1) s s where
  toFun f := ⟨source (f.1 0), ⟨List.Vector.ofFn f.1, by
    rw [List.Vector.toList_ofFn, chain_ofFn]
    refine ⟨rfl, ?_, ?_⟩
    · simpa only [finRotate_last] using f.2 (Fin.last n)
    · intro i
      have hrot : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      simpa only [hrot] using f.2 i.castSucc⟩⟩
  invFun p := ⟨p.2.1.get, by
    have hv := p.2.2
    rw [← List.Vector.ofFn_get p.2.1, List.Vector.toList_ofFn, chain_ofFn] at hv
    intro j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · rw [finRotate_last]
      exact hv.2.1.trans hv.1.symm
    · have hrot : finRotate (n + 1) i.castSucc = i.succ := finRotate_of_lt i.isLt
      rw [hrot]
      exact hv.2.2 i⟩
  left_inv f := by
    apply Subtype.ext
    funext j
    exact List.Vector.get_ofFn f.1 j
  right_inv p := by
    rcases p with ⟨s, ⟨v, hv⟩⟩
    have hs : source (v.get 0) = s := by
      have h := hv
      rw [← List.Vector.ofFn_get v, List.Vector.toList_ofFn, chain_ofFn] at h
      exact h.1
    subst s
    dsimp only
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact List.Vector.ofFn_get v

 theorem closed_card_trace {q : ℕ} (hq : 0 < q) :
    Fintype.card (ClosedWords source target q) = Matrix.trace (matrix source target ^ q) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  rw [Fintype.card_congr (closedWordEquiv source target n), Fintype.card_sigma]
  simp only [path_card, Matrix.trace, Matrix.diag]

end RigidGHZ.Supplement.Periodic.WeightedWalks
