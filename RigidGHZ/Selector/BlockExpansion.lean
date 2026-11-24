module

public import RigidGHZ.Selector.DoubleComb

/-!
# Expansion of directed vertices into nonempty ordered blocks

A moving base vertex expands into a chain; a fixed base vertex expands into
individual loops. Every cycle cover of the expanded graph compresses uniquely.
-/

@[expose] public section

namespace RigidGHZ.Selector.BlockExpansion

variable {V : Type*} (n : V → ℕ)

/-- Block `v` has `n v + 1` vertices. -/
abbrev Point := Σ v : V, Fin (n v + 1)

abbrev point (v : V) (k : ℕ) (hk : k < n v + 1) : Point n := ⟨v, ⟨k, hk⟩⟩

def first (v : V) : Point n := ⟨v, 0⟩
def last (v : V) : Point n := ⟨v, Fin.last (n v)⟩
def index (x : Point n) : ℕ := x.2.val

@[simp] theorem first_fst (v : V) : (first n v).1 = v := rfl
@[simp] theorem last_fst (v : V) : (last n v).1 = v := rfl
@[simp] theorem index_first (v : V) : index n (first n v) = 0 := rfl
@[simp] theorem index_last (v : V) : index n (last n v) = n v := rfl
@[simp] theorem index_point (v : V) (k : ℕ) (hk : k < n v + 1) :
    index n (point n v k hk) = k := rfl

 theorem point_ext {x y : Point n} (hfst : x.1 = y.1) (hindex : index n x = index n y) :
    x = y := by
  rcases x with ⟨v, k⟩
  rcases y with ⟨w, l⟩
  dsimp at hfst
  subst w
  have : k = l := Fin.ext hindex
  subst l
  rfl

 theorem eq_first_of_index_zero (x : Point n) (h : index n x = 0) : x = first n x.1 :=
  point_ext n rfl h

 theorem eq_last_of_index (x : Point n) (h : index n x = n x.1) : x = last n x.1 :=
  point_ext n rfl h

/-- The distinguished first vertex of each block. -/
def firstEmbedding : V ↪ Point n := ⟨first n, fun _ _ h => congrArg Sigma.fst h⟩

 theorem not_range_first (x : Point n) (h : index n x ≠ 0) :
    x ∉ Set.range (firstEmbedding n) := by
  rintro ⟨v, hv⟩
  exact h (congrArg (index n) hv).symm

/-- A permutation expands by rotating each moving block and sending its end to
the first vertex of the next block. -/
noncomputable def lift (q : Equiv.Perm V) : Equiv.Perm (Point n) := by
  classical
  exact (Equiv.sigmaCongrRight (fun v =>
    if q v = v then Equiv.refl (Fin (n v + 1)) else finRotate (n v + 1))).trans
    (q.viaEmbedding (firstEmbedding n))

 theorem lift_apply_fixed (q : Equiv.Perm V) (v : V) (k : Fin (n v + 1))
    (h : q v = v) : lift n q ⟨v, k⟩ = ⟨v, k⟩ := by
  classical
  change q.viaEmbedding (firstEmbedding n)
    (⟨v, (if q v = v then Equiv.refl _ else finRotate _) k⟩ : Point n) = _
  rw [ite_eq_left h]
  change q.viaEmbedding (firstEmbedding n) ⟨v, k⟩ = ⟨v, k⟩
  by_cases hk : k = 0
  · subst k
    change q.viaEmbedding (firstEmbedding n) (firstEmbedding n v) = first n v
    rw [Equiv.Perm.viaEmbedding_apply, h]
    rfl
  · apply Equiv.Perm.viaEmbedding_apply_of_notMem
    exact not_range_first n _ (fun hh => hk (Fin.ext hh))

 theorem lift_apply_next (q : Equiv.Perm V) (v : V) (k : Fin (n v + 1))
    (h : q v ≠ v) (hk : k.val < n v) :
    lift n q ⟨v, k⟩ = point n v (k.val + 1) (by omega) := by
  classical
  change q.viaEmbedding (firstEmbedding n)
    (⟨v, (if q v = v then Equiv.refl _ else finRotate _) k⟩ : Point n) = _
  rw [ite_eq_right h]
  rcases k with ⟨k, hk'⟩
  rw [finRotate_of_lt hk]
  apply Equiv.Perm.viaEmbedding_apply_of_notMem
  exact not_range_first n _ (by simp)

 theorem lift_apply_last (q : Equiv.Perm V) (v : V) (h : q v ≠ v) :
    lift n q (last n v) = first n (q v) := by
  classical
  change q.viaEmbedding (firstEmbedding n)
    (⟨v, (if q v = v then Equiv.refl _ else finRotate _) (Fin.last (n v))⟩ : Point n) = _
  rw [ite_eq_right h, finRotate_last]
  exact Equiv.Perm.viaEmbedding_apply _ _ _

/-- Expanded graph: loops, internal chain arcs, and last-to-first base arcs. -/
def Arc (A : V → V → Prop) (x y : Point n) : Prop :=
  (A x.1 x.1 ∧ y = x) ∨
  (∃ h : index n x < n x.1,
    y = point n x.1 (index n x + 1) (by omega)) ∨
  (index n x = n x.1 ∧ index n y = 0 ∧ x.1 ≠ y.1 ∧ A x.1 y.1)

 theorem lift_cover (A : V → V → Prop) (q : Equiv.Perm V)
    (hq : ∀ v, A v (q v)) : ∀ x, Arc n A x (lift n q x) := by
  rintro ⟨v, k⟩
  by_cases hfix : q v = v
  · rw [lift_apply_fixed n q v k hfix]
    exact Or.inl ⟨by simpa [hfix] using hq v, rfl⟩
  · by_cases hk : k.val < n v
    · rw [lift_apply_next n q v k hfix hk]
      exact Or.inr (Or.inl ⟨hk, rfl⟩)
    · have hlast : (⟨v, k⟩ : Point n) = last n v := point_ext n rfl (by dsimp [index]; omega)
      rw [hlast, lift_apply_last n q v hfix]
      exact Or.inr (Or.inr ⟨rfl, rfl, Ne.symm hfix, hq v⟩)

 theorem lift_moves_iff (q : Equiv.Perm V) (x : Point n) :
    lift n q x ≠ x ↔ q x.1 ≠ x.1 := by
  rcases x with ⟨v, k⟩
  by_cases hq : q v = v
  · rw [lift_apply_fixed n q v k hq]
    simp [hq]
  · have hm : lift n q ⟨v, k⟩ ≠ ⟨v, k⟩ := by
      by_cases hk : k.val < n v
      · rw [lift_apply_next n q v k hq hk]
        intro heq
        have := congrArg (index n) heq
        dsimp [index] at this
        omega
      · have hlast : (⟨v, k⟩ : Point n) = last n v := point_ext n rfl (by dsimp [index]; omega)
        rw [hlast, lift_apply_last n q v hq]
        intro heq
        exact hq (congrArg Sigma.fst heq)
    exact iff_of_true hm hq

 theorem lift_last_fst (q : Equiv.Perm V) (v : V) :
    (lift n q (last n v)).1 = q v := by
  by_cases hq : q v = v
  · change (lift n q ⟨v, Fin.last (n v)⟩).1 = q v
    rw [lift_apply_fixed n q v _ hq]
    exact hq.symm
  · rw [lift_apply_last n q v hq]
    rfl

 theorem lift_injective : Function.Injective (lift n) := by
  intro p q h
  apply Equiv.ext
  intro v
  have he := congrArg (fun e : Equiv.Perm (Point n) => (e (last n v)).1) h
  simpa only [lift_last_fst] using he

variable {n} {A : V → V → Prop} (Q : Equiv.Perm (Point n))
    (hQ : ∀ x, Arc n A x (Q x))

include hQ

 theorem next_of_moved (x : Point n) (hx : Q x ≠ x) (hk : index n x < n x.1) :
    Q x = point n x.1 (index n x + 1) (by omega) := by
  rcases hQ x with h | ⟨h, heq⟩ | h
  · exact (hx h.2).elim
  · exact heq
  · omega

 theorem predecessor_of_moved (v : V) (k : ℕ) (hk : k + 1 < n v + 1)
    (hm : Q (point n v (k + 1) hk) ≠ point n v (k + 1) hk) :
    Q (point n v k (by omega)) = point n v (k + 1) hk := by
  let x := point n v (k + 1) hk
  let y := Q.symm x
  have hpred : Q y = x := Q.apply_symm_apply x
  have hyx : y ≠ x := by
    intro h
    apply hm
    change Q x = x
    rwa [h] at hpred
  have hA : Arc n A y x := by rw [← hpred]; exact hQ y
  rcases hA with h | ⟨h, heq⟩ | h
  · exact (hyx h.2.symm).elim
  · have hyv : y.1 = v := (congrArg Sigma.fst heq).symm
    have hyk : index n y = k := by
      have heqi := congrArg (index n) heq
      dsimp [x, index, point] at heqi
      change y.2.val = k
      omega
    have hy : y = point n v k (by omega) := point_ext n hyv hyk
    rwa [hy] at hpred
  · have : k + 1 = 0 := h.2.1
    omega

 theorem moved_succ_iff (v : V) (k : ℕ) (hk : k + 1 < n v + 1) :
    (Q (point n v (k + 1) hk) ≠ point n v (k + 1) hk) ↔
      Q (point n v k (by omega)) ≠ point n v k (by omega) := by
  have hne : point n v k (by omega) ≠ point n v (k + 1) hk := by
    intro h
    have := congrArg (index n) h
    simp only [index_point] at this
    omega
  constructor
  · intro hm hfix
    have hnext := predecessor_of_moved Q hQ v k hk hm
    exact hne (hfix.symm.trans hnext)
  · intro hm
    have hnext := next_of_moved Q hQ (point n v k (by omega)) hm (by dsimp [index]; omega)
    exact DoubleComb.moved_of_predecessor Q hnext hne

 theorem moved_iff_first (v : V) (k : Fin (n v + 1)) :
    (Q (⟨v, k⟩ : Point n) ≠ ⟨v, k⟩) ↔ Q (first n v) ≠ first n v := by
  suffices ∀ k : ℕ, ∀ hk : k < n v + 1,
      (Q (point n v k hk) ≠ point n v k hk) ↔ Q (first n v) ≠ first n v by
    exact this k.val k.isLt
  intro k
  induction k with
  | zero => intro hk; rfl
  | succ k ih =>
    intro hk
    exact (moved_succ_iff Q hQ v k hk).trans (ih (by omega))

 theorem fixed_of_last_fixed (v : V) (h : Q (last n v) = last n v)
    (k : Fin (n v + 1)) : Q (⟨v, k⟩ : Point n) = ⟨v, k⟩ := by
  by_contra hm
  have hm0 := (moved_iff_first Q hQ v k).mp hm
  exact (moved_iff_first Q hQ v (Fin.last (n v))).mpr hm0 h

 theorem moved_of_last_moved (v : V) (h : Q (last n v) ≠ last n v)
    (k : Fin (n v + 1)) : Q (⟨v, k⟩ : Point n) ≠ ⟨v, k⟩ :=
  (moved_iff_first Q hQ v k).mpr ((moved_iff_first Q hQ v (Fin.last (n v))).mp h)

omit hQ in
/-- Compression sends a block to the block entered from its end. -/
def compressMap (v : V) : V := (Q (last n v)).1

 theorem compressMap_fixed_iff (v : V) :
    compressMap Q v = v ↔ Q (last n v) = last n v := by
  constructor
  · intro h
    rcases hQ (last n v) with hh | ⟨hh, _⟩ | hh
    · exact hh.2
    · simp [index_last] at hh
    · exact (hh.2.2.1 h.symm).elim
  · intro h
    exact congrArg Sigma.fst h

 theorem last_to_first (v : V) (h : compressMap Q v ≠ v) :
    Q (last n v) = first n (compressMap Q v) := by
  rcases hQ (last n v) with hh | ⟨hh, _⟩ | hh
  · exact (h (congrArg Sigma.fst hh.2)).elim
  · simp [index_last] at hh
  · exact eq_first_of_index_zero n _ hh.2.1

 theorem compressMap_injective : Function.Injective (compressMap Q) := by
  intro v w hvw
  classical
  let e : V → Point n := fun v => if compressMap Q v = v then first n v else last n v
  have he : ∀ v, Q (e v) = first n (compressMap Q v) := by
    intro v
    dsimp [e]
    split_ifs with h
    · rw [h]
      exact fixed_of_last_fixed Q hQ v ((compressMap_fixed_iff Q hQ v).mp h) 0
    · exact last_to_first Q hQ v h
  have hefst : ∀ v, (e v).1 = v := by intro v; dsimp [e]; split_ifs <;> rfl
  have heq : e v = e w := Q.injective ((he v).trans ((congrArg (first n) hvw).trans (he w).symm))
  have hf := congrArg Sigma.fst heq
  simpa only [hefst] using hf

/-- The ordinary permutation induced on blocks by any expanded cycle cover. -/
noncomputable def compress [Fintype V] : Equiv.Perm V :=
  Equiv.ofBijective (compressMap Q) ((Finite.injective_iff_bijective).mp (compressMap_injective Q hQ))

 theorem compress_cover [Fintype V] : ∀ v, A v (compress Q hQ v) := by
  intro v
  rcases hQ (last n v) with h | ⟨h, _⟩ | h
  · change A v (compressMap Q v)
    rw [(compressMap_fixed_iff Q hQ v).mpr h.2]
    exact h.1
  · simp [index_last] at h
  · exact h.2.2.2

 theorem lift_compress [Fintype V] : lift n (compress Q hQ) = Q := by
  apply Equiv.ext
  rintro ⟨v, k⟩
  by_cases hfix : compressMap Q v = v
  · rw [lift_apply_fixed n (compress Q hQ) v k hfix]
    exact (fixed_of_last_fixed Q hQ v ((compressMap_fixed_iff Q hQ v).mp hfix) k).symm
  · by_cases hk : k.val < n v
    · rw [lift_apply_next n (compress Q hQ) v k hfix hk]
      exact (next_of_moved Q hQ _
        (moved_of_last_moved Q hQ v (mt (compressMap_fixed_iff Q hQ v).mpr hfix) k) hk).symm
    · have hlast : (⟨v, k⟩ : Point n) = last n v := point_ext n rfl (by dsimp [index]; omega)
      rw [hlast, lift_apply_last n (compress Q hQ) v hfix]
      exact (last_to_first Q hQ v hfix).symm

end RigidGHZ.Selector.BlockExpansion
