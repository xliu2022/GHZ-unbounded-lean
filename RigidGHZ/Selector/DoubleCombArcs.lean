module

public import RigidGHZ.Selector.ExpandedDoubleComb

@[expose] public section

namespace RigidGHZ.Selector.DoubleComb

open Vertex BlockExpansion

variable {R : Type*} {T : ℕ} (n : Vertex R T → ℕ)

/-- Source of the shared arc entering a vertex of a full-row or suffix block. -/
def upperSource (i : R) (a : Fin (T + 1)) (k : Fin (n (upper i a) + 1)) : Point n :=
  if hk : k.val = 0 then
    if ha : a.val = 0 then last n hub
    else last n (upper i ⟨a.val - 1, by omega⟩)
  else point n (upper i a) (k.val - 1) (by omega)

 theorem upperSource_ne (i : R) (a : Fin (T + 1)) (k : Fin (n (upper i a) + 1)) :
    upperSource n i a k ≠ (⟨upper i a, k⟩ : Point n) := by
  unfold upperSource
  split_ifs with hk ha
  · intro h; have := congrArg Sigma.fst h; cases this
  · intro h
    have heq := congrArg Sigma.fst h
    have heq' := congrArg Fin.val (Vertex.upper.inj heq).2
    dsimp at heq'
    omega
  · intro h
    have hi := congrArg (index n) h
    dsimp [index] at hi
    omega

 theorem upperSource_not_private (i : R) (a : Fin (T + 1))
    (k : Fin (n (upper i a) + 1)) : ¬ IsPrivate (upperSource n i a k).1 := by
  unfold upperSource
  split_ifs <;> simp [last, IsPrivate]

 theorem upper_arc_shared (i : R) (a : Fin (T + 1)) (k : Fin (n (upper i a) + 1)) :
    Shared n (upperSource n i a k) ⟨upper i a, k⟩ :=
  Or.inr ⟨upperSource_not_private n i a k, by simp [IsPrivate]⟩

/-- The arc entering each upper-block vertex occurs exactly at its full-row or
suffix pattern. -/
theorem upper_arc_occurs_iff (j : R) (b : Fin (T + 1)) (i : R)
    (a : Fin (T + 1)) (k : Fin (n (upper i a) + 1)) :
    expandedPerm n j b (upperSource n i a k) = (⟨upper i a, k⟩ : Point n) ↔
      i = j ∧ a.val ≤ b.val := by
  constructor
  · intro h
    have hm := moved_of_predecessor (expandedPerm n j b) h (upperSource_ne n i a k)
    exact (expandedPerm_moves_iff n j b _).mp hm
  · rintro ⟨hij, hab⟩
    subst i
    have hactive : routePerm j b (upper j a) ≠ upper j a :=
      (routePerm_moves_iff j b _).mpr ⟨rfl, hab⟩
    unfold upperSource
    split_ifs with hk ha
    · have ha0 : a = 0 := Fin.ext ha
      subst a
      have hm : routePerm j b hub ≠ hub := (routePerm_moves_iff j b _).mpr trivial
      change lift n (routePerm j b) (last n hub) = _
      rw [lift_apply_last n _ hub hm,
        routePerm_apply_onRoute j b hub trivial]
      apply point_ext n
      · rfl
      · exact hk.symm
    · let a' : Fin (T + 1) := ⟨a.val - 1, by omega⟩
      have ha' : a'.val < b.val := by dsimp [a']; omega
      have hp : routePerm j b (upper j a') = upper j a := by
        rw [routePerm_apply_onRoute j b (upper j a') ⟨rfl, Nat.le_of_lt ha'⟩]
        simp only [step, ha', dite_eq_left]
        congr 1
        apply Fin.ext
        dsimp [a']
        omega
      have hm : routePerm j b (upper j a') ≠ upper j a' :=
        (routePerm_moves_iff j b _).mpr ⟨rfl, Nat.le_of_lt ha'⟩
      change lift n (routePerm j b) (last n (upper j a')) = _
      rw [lift_apply_last n _ _ hm, hp]
      exact point_ext n rfl hk.symm
    · change lift n (routePerm j b) (point n (upper j a) (k.val - 1) _) = _
      rw [lift_apply_next n _ _ _ hactive (by dsimp; omega)]
      apply point_ext n
      · rfl
      · dsimp [index]
        omega

/-- Compressed successor of a prefix block. -/
def lowerNext (i : R) (a : Fin T) : Vertex R T :=
  if h : a.val + 1 < T then lower i ⟨a.val + 1, h⟩ else hub

/-- Target of the shared arc leaving a prefix-block vertex. -/
def lowerTarget (i : R) (a : Fin T) (k : Fin (n (lower i a) + 1)) : Point n :=
  if hk : k.val < n (lower i a) then point n (lower i a) (k.val + 1) (by omega)
  else first n (lowerNext i a)

 theorem lowerNext_ne (i : R) (a : Fin T) : lowerNext i a ≠ lower i a := by
  unfold lowerNext
  split_ifs <;> simp [Fin.ext_iff]

 theorem lowerTarget_ne (i : R) (a : Fin T) (k : Fin (n (lower i a) + 1)) :
    lowerTarget n i a k ≠ (⟨lower i a, k⟩ : Point n) := by
  unfold lowerTarget
  split_ifs with hk
  · intro h
    have hi := congrArg (index n) h
    dsimp [index] at hi
    omega
  · intro h
    exact lowerNext_ne i a (congrArg Sigma.fst h)

 theorem lowerTarget_not_private (i : R) (a : Fin T)
    (k : Fin (n (lower i a) + 1)) : ¬ IsPrivate (lowerTarget n i a k).1 := by
  unfold lowerTarget lowerNext
  split_ifs <;> simp [first, IsPrivate]

 theorem lower_arc_shared (i : R) (a : Fin T) (k : Fin (n (lower i a) + 1)) :
    Shared n ⟨lower i a, k⟩ (lowerTarget n i a k) :=
  Or.inr ⟨by simp [IsPrivate], lowerTarget_not_private n i a k⟩

/-- The arc leaving each lower-block vertex occurs exactly at its prefix pattern. -/
theorem lower_arc_occurs_iff (j : R) (b : Fin (T + 1)) (i : R)
    (a : Fin T) (k : Fin (n (lower i a) + 1)) :
    expandedPerm n j b ⟨lower i a, k⟩ = lowerTarget n i a k ↔
      i = j ∧ b.val ≤ a.val := by
  constructor
  · intro h
    have hm : expandedPerm n j b (⟨lower i a, k⟩ : Point n) ≠ ⟨lower i a, k⟩ := by
      rw [h]
      exact lowerTarget_ne n i a k
    exact (expandedPerm_moves_iff n j b _).mp hm
  · rintro ⟨hij, hab⟩
    subst i
    have hactive : routePerm j b (lower j a) ≠ lower j a :=
      (routePerm_moves_iff j b _).mpr ⟨rfl, hab⟩
    have hstep : routePerm j b (lower j a) = lowerNext j a :=
      routePerm_apply_onRoute j b _ ⟨rfl, hab⟩
    unfold lowerTarget
    split_ifs with hk
    · exact lift_apply_next n _ _ k hactive hk
    · have hx : (⟨lower j a, k⟩ : Point n) = last n (lower j a) :=
        point_ext n rfl (by dsimp [index]; omega)
      change lift n (routePerm j b) _ = _
      rw [hx, lift_apply_last n _ _ hactive, hstep]

variable [DecidableEq R]

/-- One shared arc per upper-chain owner, including the arc entering the chain. -/
def upperArcs (i : R) (a : Fin (T + 1)) : Finset (Point n × Point n) :=
  Finset.univ.image (fun k : Fin (n (upper i a) + 1) =>
    (upperSource n i a k, ⟨upper i a, k⟩))

/-- One shared arc per lower-chain owner, including the arc leaving the chain. -/
def lowerArcs (i : R) (a : Fin T) : Finset (Point n × Point n) :=
  Finset.univ.image (fun k : Fin (n (lower i a) + 1) =>
    (⟨lower i a, k⟩, lowerTarget n i a k))

@[simp] theorem upperArcs_card (i : R) (a : Fin (T + 1)) :
    (upperArcs n i a).card = n (upper i a) + 1 := by
  rw [upperArcs, Finset.card_image_of_injective]
  · simp
  · intro k l h
    have hs := congrArg (fun ab : Point n × Point n => index n ab.2) h
    exact Fin.ext hs

@[simp] theorem lowerArcs_card (i : R) (a : Fin T) :
    (lowerArcs n i a).card = n (lower i a) + 1 := by
  rw [lowerArcs, Finset.card_image_of_injective]
  · simp
  · intro k l h
    have hs := congrArg (fun ab : Point n × Point n => index n ab.1) h
    exact Fin.ext hs

 theorem upperArcs_occurs_iff (j : R) (b : Fin (T + 1)) (i : R)
    (a : Fin (T + 1)) {x y : Point n} (hxy : (x, y) ∈ upperArcs n i a) :
    expandedPerm n j b x = y ↔ i = j ∧ a.val ≤ b.val := by
  obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hxy
  have hx : upperSource n i a k = x := congrArg Prod.fst heq
  have hy : (⟨upper i a, k⟩ : Point n) = y := congrArg Prod.snd heq
  rw [← hx, ← hy]
  exact upper_arc_occurs_iff n j b i a k

 theorem lowerArcs_occurs_iff (j : R) (b : Fin (T + 1)) (i : R)
    (a : Fin T) {x y : Point n} (hxy : (x, y) ∈ lowerArcs n i a) :
    expandedPerm n j b x = y ↔ i = j ∧ b.val ≤ a.val := by
  obtain ⟨k, _, heq⟩ := Finset.mem_image.mp hxy
  have hx : (⟨lower i a, k⟩ : Point n) = x := congrArg Prod.fst heq
  have hy : lowerTarget n i a k = y := congrArg Prod.snd heq
  rw [← hx, ← hy]
  exact lower_arc_occurs_iff n j b i a k

/-- The two orientations that identify all non-private shared arcs. -/
def IsUpper : Vertex R T → Prop
  | upper _ _ => True
  | _ => False

def IsLower : Vertex R T → Prop
  | lower _ _ => True
  | _ => False

 theorem shared_nonloop_shape (hHub : n hub = 0) {x y : Point n}
    (hA : BlockExpansion.Arc n DoubleComb.Arc x y) (hS : Shared n x y) (hne : x ≠ y) :
    IsUpper y.1 ∨ IsLower x.1 := by
  have hnprivate := hS.resolve_left hne
  rcases x with ⟨v, k⟩
  cases v with
  | hub =>
    rcases hA with h | ⟨h, he⟩ | h
    · exact (hne h.2.symm).elim
    · change k.val < n hub at h
      omega
    · obtain ⟨i, hi⟩ := h.2.2.2
      left
      rw [hi]
      trivial
  | upper i a =>
    rcases hA with h | ⟨h, he⟩ | h
    · exact (hne h.2.symm).elim
    · subst y; exact Or.inl trivial
    · rcases h.2.2.2 with hy | hy | ⟨_, hy⟩
      · left; rw [hy]; trivial
      · exact (hnprivate.2 (by rw [hy]; trivial)).elim
      · left; rw [hy]; trivial
  | branch i a => exact (hnprivate.1 trivial).elim
  | lower i a => exact Or.inr trivial

 theorem exists_upper_point (x : Point n) (hx : IsUpper x.1) :
    ∃ i a k, x = (⟨upper i a, k⟩ : Point n) := by
  rcases x with ⟨v, k⟩
  cases v with
  | upper i a => exact ⟨i, a, k, rfl⟩
  | _ => exact hx.elim

 theorem exists_lower_point (x : Point n) (hx : IsLower x.1) :
    ∃ i a k, x = (⟨lower i a, k⟩ : Point n) := by
  rcases x with ⟨v, k⟩
  cases v with
  | lower i a => exact ⟨i, a, k, rfl⟩
  | _ => exact hx.elim

/-- There are no unaccounted shared arcs: every nonloop shared arc is exactly
one of the incoming upper arcs or outgoing lower arcs already counted above. -/
theorem shared_arc_cases (hHub : n hub = 0) (i : R) (b : Fin (T + 1))
    (x : Point n) (hS : Shared n x (expandedPerm n i b x)) :
    expandedPerm n i b x = x ∨
      (∃ j a, (x, expandedPerm n i b x) ∈ upperArcs n j a) ∨
      (∃ j a, (x, expandedPerm n i b x) ∈ lowerArcs n j a) := by
  by_cases hfix : expandedPerm n i b x = x
  · exact Or.inl hfix
  · have hshape := shared_nonloop_shape n hHub (expandedPerm_cover n i b x) hS (Ne.symm hfix)
    rcases hshape with hu | hl
    · obtain ⟨j, a, k, he⟩ := exists_upper_point n _ hu
      have hm := moved_of_predecessor (expandedPerm n i b) he
        (by intro h; exact hfix (he.trans h.symm))
      have hp := (expandedPerm_moves_iff n i b _).mp hm
      have hs := (upper_arc_occurs_iff n i b j a k).mpr hp
      have hx : x = upperSource n j a k := (expandedPerm n i b).injective (he.trans hs.symm)
      refine Or.inr (Or.inl ⟨j, a, ?_⟩)
      apply Finset.mem_image.mpr
      exact ⟨k, Finset.mem_univ _, Prod.ext hx.symm he.symm⟩
    · obtain ⟨j, a, k, rfl⟩ := exists_lower_point n x hl
      have hp := (expandedPerm_moves_iff n i b _).mp hfix
      have ht := (lower_arc_occurs_iff n i b j a k).mpr hp
      refine Or.inr (Or.inr ⟨j, a, ?_⟩)
      exact Finset.mem_image.mpr ⟨k, Finset.mem_univ _, Prod.ext rfl ht.symm⟩

variable [Fintype R]

/-- The concrete finite set on which shared anchors must be assigned. -/
def sharedArcs : Finset (Point n × Point n) :=
  (Finset.univ.image (fun x : Point n => (x, x))) ∪
    ((Finset.univ : Finset R).biUnion (fun i => Finset.univ.biUnion (upperArcs n i))) ∪
    ((Finset.univ : Finset R).biUnion (fun i => Finset.univ.biUnion (lowerArcs n i)))

 theorem mem_sharedArcs_iff {x y : Point n} :
    (x, y) ∈ sharedArcs n ↔ x = y ∨
      (∃ i a, (x, y) ∈ upperArcs n i a) ∨ (∃ i a, (x, y) ∈ lowerArcs n i a) := by
  simp only [sharedArcs, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion,
    Finset.mem_univ, true_and, Prod.mk.injEq]
  aesop

 theorem sharedArcs_are_shared {x y : Point n} (h : (x, y) ∈ sharedArcs n) : Shared n x y := by
  rcases (mem_sharedArcs_iff n).mp h with h | ⟨i, a, h⟩ | ⟨i, a, h⟩
  · exact Or.inl h
  · obtain ⟨k, _, he⟩ := Finset.mem_image.mp h
    have hh := upper_arc_shared n i a k
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rwa [hx, hy] at hh
  · obtain ⟨k, _, he⟩ := Finset.mem_image.mp h
    have hh := lower_arc_shared n i a k
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rwa [hx, hy] at hh

 theorem sharedArcs_private_unique (hHub : n hub = 0)
    (ib jc : R × Fin (T + 1)) (x : Point n)
    (hp : (x, expandedPerm n ib.1 ib.2 x) ∉ sharedArcs n)
    (heq : expandedPerm n ib.1 ib.2 x = expandedPerm n jc.1 jc.2 x) : ib = jc := by
  apply expanded_private_unique n ib jc x _ heq
  intro hS
  apply hp
  apply (mem_sharedArcs_iff n).mpr
  rcases shared_arc_cases n hHub ib.1 ib.2 x hS with h | h | h
  · exact Or.inl h.symm
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

end RigidGHZ.Selector.DoubleComb
