module

public import RigidGHZ.Selector.PlanarComb
public import RigidGHZ.Construction.PlanarPatterns

/-! One shared arc per owner in the no-full-chain planar comb. -/

@[expose] public section

namespace RigidGHZ.Selector.PlanarComb

open Equiv Equiv.Perm BlockExpansion

variable {T : ℕ}

def up (a : Fin (T + 1)) : Vertex T := ⟨.upper () a, by simp⟩

@[simp] theorem up_zero : up (0 : Fin (T + 1)) = hub T := rfl

theorem up_injective : Function.Injective (up : Fin (T + 1) → Vertex T) := by
  intro a b h
  exact (DoubleComb.Vertex.upper.inj (congrArg Subtype.val h)).2

theorem route_up_next (b a : Fin (T + 1)) (hab : a.val < b.val) :
    routePerm b (up a) = up ⟨a.val + 1, by omega⟩ := by
  apply Subtype.ext
  change swap DoubleComb.Vertex.hub (DoubleComb.Vertex.upper () 0)
    (DoubleComb.routePerm () b (.upper () a)) = DoubleComb.Vertex.upper () ⟨a.val + 1, by omega⟩
  rw [DoubleComb.routePerm_apply_onRoute () b (.upper () a) ⟨rfl, Nat.le_of_lt hab⟩]
  have hs : DoubleComb.step () b (.upper () a) =
      DoubleComb.Vertex.upper () ⟨a.val + 1, by omega⟩ := by
    simp [DoubleComb.step, hab]
  rw [hs]
  apply swap_apply_of_ne_of_ne
  · intro he; cases he
  · intro he
    have hi := congrArg Fin.val (DoubleComb.Vertex.upper.inj he).2
    dsimp at hi
    omega

theorem route_up_exit (b : Fin (T + 1)) : routePerm b (up b) = branch b := by
  apply Subtype.ext
  change swap DoubleComb.Vertex.hub (DoubleComb.Vertex.upper () 0)
    (DoubleComb.routePerm () b (.upper () b)) = DoubleComb.Vertex.branch () b
  rw [DoubleComb.routePerm_apply_onRoute () b (.upper () b) ⟨rfl, le_rfl⟩]
  simp [DoubleComb.step, swap_apply_of_ne_of_ne]

def prefixNext (a : Fin T) : Vertex T :=
  if h : a.val + 1 < T then prefixBlock ⟨a.val + 1, h⟩ else hub T

theorem route_prefix_next (b : Fin (T + 1)) (a : Fin T) (hba : b.val ≤ a.val) :
    routePerm b (prefixBlock a) = prefixNext a := by
  apply Subtype.ext
  change swap DoubleComb.Vertex.hub (DoubleComb.Vertex.upper () 0)
    (DoubleComb.routePerm () b (.lower () a)) = (prefixNext a).val
  rw [DoubleComb.routePerm_apply_onRoute () b (.lower () a) ⟨rfl, hba⟩]
  by_cases ha : a.val + 1 < T
  · simp [DoubleComb.step, prefixNext, prefixBlock, ha, swap_apply_of_ne_of_ne]
  · simp [DoubleComb.step, prefixNext, hub, ha]

theorem route_branch_next (b : Fin (T + 1)) :
    routePerm b (branch b) = if h : b.val < T then prefixBlock ⟨b.val, h⟩ else hub T := by
  apply Subtype.ext
  change swap DoubleComb.Vertex.hub (DoubleComb.Vertex.upper () 0)
    (DoubleComb.routePerm () b (.branch () b)) = _
  rw [DoubleComb.routePerm_apply_onRoute () b (.branch () b) ⟨rfl, rfl⟩]
  by_cases hb : b.val < T
  · simp [DoubleComb.step, prefixBlock, hb, swap_apply_of_ne_of_ne]
  · simp [DoubleComb.step, hub, hb]

theorem prefixNext_ne (a : Fin T) : prefixNext a ≠ prefixBlock a := by
  unfold prefixNext
  split_ifs with ha
  · intro h
    have he := congrArg Subtype.val h
    have hi := congrArg Fin.val (DoubleComb.Vertex.lower.inj he).2
    dsimp at hi
    omega
  · intro h
    have he := congrArg Subtype.val h
    cases he

variable (n : Vertex T → ℕ)

def upperSource (a : Fin T) (k : Fin (n (suffix a) + 1)) : Point n :=
  if hk : k.val = 0 then last n (up ⟨a.val, by omega⟩)
  else point n (suffix a) (k.val - 1) (by omega)

theorem upperSource_ne (a : Fin T) (k : Fin (n (suffix a) + 1)) :
    upperSource n a k ≠ (⟨suffix a, k⟩ : Point n) := by
  unfold upperSource
  split_ifs with hk
  · intro h
    have he := congrArg (fun x : Point n => x.1.val) h
    have hi := congrArg Fin.val (DoubleComb.Vertex.upper.inj he).2
    dsimp at hi
    omega
  · intro h
    have hi := congrArg (index n) h
    dsimp [index] at hi
    omega

theorem upper_arc_occurs_iff (b : Fin (T + 1)) (a : Fin T)
    (k : Fin (n (suffix a) + 1)) :
    expandedPerm n b (upperSource n a k) = (⟨suffix a, k⟩ : Point n) ↔ a.val < b.val := by
  constructor
  · intro h
    have hm := DoubleComb.moved_of_predecessor (expandedPerm n b) h (upperSource_ne n a k)
    have hh := (expandedPerm_moves_iff n b _).mp hm
    simp only [suffix, DoubleComb.OnRoute, true_and] at hh
    omega
  · intro hab
    have hactive : routePerm b (suffix a) ≠ suffix a := (suffix_moves b a).mpr hab
    unfold upperSource
    split_ifs with hk
    · have hpred : routePerm b (up ⟨a.val, by omega⟩) ≠ up ⟨a.val, by omega⟩ :=
        (routePerm_moves_iff b _).mpr ⟨rfl, Nat.le_of_lt hab⟩
      change lift n (routePerm b) (last n _) = _
      rw [lift_apply_last n _ _ hpred, route_up_next b _ hab]
      exact point_ext n rfl hk.symm
    · change lift n (routePerm b) (point n (suffix a) (k.val - 1) _) = _
      rw [lift_apply_next n _ _ _ hactive (by dsimp; omega)]
      exact point_ext n rfl (by dsimp [index]; omega)

def lowerTarget (a : Fin T) (k : Fin (n (prefixBlock a) + 1)) : Point n :=
  if hk : k.val < n (prefixBlock a) then point n (prefixBlock a) (k.val + 1) (by omega)
  else first n (prefixNext a)

theorem lowerTarget_ne (a : Fin T) (k : Fin (n (prefixBlock a) + 1)) :
    lowerTarget n a k ≠ (⟨prefixBlock a, k⟩ : Point n) := by
  unfold lowerTarget
  split_ifs with hk
  · intro h
    have hi := congrArg (index n) h
    dsimp [index] at hi
    omega
  · intro h
    exact prefixNext_ne a (congrArg Sigma.fst h)

theorem lower_arc_occurs_iff (b : Fin (T + 1)) (a : Fin T)
    (k : Fin (n (prefixBlock a) + 1)) :
    expandedPerm n b (⟨prefixBlock a, k⟩ : Point n) = lowerTarget n a k ↔ b.val ≤ a.val := by
  constructor
  · intro h
    have hm : expandedPerm n b (⟨prefixBlock a, k⟩ : Point n) ≠ ⟨prefixBlock a, k⟩ := by
      rw [h]
      exact lowerTarget_ne n a k
    simpa only [prefixBlock, DoubleComb.OnRoute, true_and] using (expandedPerm_moves_iff n b _).mp hm
  · intro hba
    have hactive : routePerm b (prefixBlock a) ≠ prefixBlock a := (prefix_moves b a).mpr hba
    unfold lowerTarget
    split_ifs with hk
    · exact lift_apply_next n _ _ k hactive hk
    · have hx : (⟨prefixBlock a, k⟩ : Point n) = last n (prefixBlock a) :=
        point_ext n rfl (by dsimp [index]; omega)
      change lift n (routePerm b) _ = _
      rw [hx, lift_apply_last n _ _ hactive, route_prefix_next b a hba]

def upperArcs (a : Fin T) : Finset (Point n × Point n) :=
  Finset.univ.image (fun k : Fin (n (suffix a) + 1) => (upperSource n a k, ⟨suffix a, k⟩))

def lowerArcs (a : Fin T) : Finset (Point n × Point n) :=
  Finset.univ.image (fun k : Fin (n (prefixBlock a) + 1) => (⟨prefixBlock a, k⟩, lowerTarget n a k))

def ownerBlock : Planar.Pattern T → Vertex T
  | .prefix a => prefixBlock a
  | .suffix a => suffix a

def sharedArcs : Planar.Pattern T → Finset (Point n × Point n)
  | .prefix a => lowerArcs n a
  | .suffix a => upperArcs n a

@[simp] theorem upperArcs_card (a : Fin T) : (upperArcs n a).card = n (suffix a) + 1 := by
  rw [upperArcs, Finset.card_image_of_injective]
  · simp
  · intro k l h
    exact Fin.ext (congrArg (fun ab : Point n × Point n => index n ab.2) h)

@[simp] theorem lowerArcs_card (a : Fin T) : (lowerArcs n a).card = n (prefixBlock a) + 1 := by
  rw [lowerArcs, Finset.card_image_of_injective]
  · simp
  · intro k l h
    exact Fin.ext (congrArg (fun ab : Point n × Point n => index n ab.1) h)

@[simp] theorem sharedArcs_card (p : Planar.Pattern T) :
    (sharedArcs n p).card = n (ownerBlock p) + 1 := by
  cases p <;> simp [sharedArcs, ownerBlock]

theorem sharedArcs_nonloop (p : Planar.Pattern T) (x y : Point n) (hxy : (x, y) ∈ sharedArcs n p) :
    x ≠ y := by
  cases p with
  | «prefix» a =>
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hxy
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rw [← hx, ← hy]
    exact Ne.symm (lowerTarget_ne n a k)
  | «suffix» a =>
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hxy
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rw [← hx, ← hy]
    exact upperSource_ne n a k

theorem sharedArcs_occurs_iff (b : Fin (T + 1)) (p : Planar.Pattern T)
    {x y : Point n} (hxy : (x, y) ∈ sharedArcs n p) :
    expandedPerm n b x = y ↔ p.occurs b.val := by
  cases p with
  | «prefix» a =>
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hxy
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rw [← hx, ← hy]
    exact lower_arc_occurs_iff n b a k
  | «suffix» a =>
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp hxy
    have hx := congrArg Prod.fst he
    have hy := congrArg Prod.snd he
    dsimp at hx hy
    rw [← hx, ← hy]
    exact upper_arc_occurs_iff n b a k

theorem upperSource_not_lower (a c : Fin T) (k : Fin (n (suffix a) + 1)) :
    (upperSource n a k).1 ≠ prefixBlock c := by
  unfold upperSource
  split_ifs <;> intro h <;> have he := congrArg Subtype.val h <;> cases he

theorem sharedArcs_disjoint :
    Pairwise (fun p q : Planar.Pattern T => Disjoint (sharedArcs n p) (sharedArcs n q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  rintro ⟨x, y⟩ hx hy
  cases p with
  | «prefix» a =>
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hx
    cases q with
    | «prefix» c =>
      obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp hy
      have he := congrArg (fun ab : Point n × Point n => ab.1.1.val) (hke.trans hle.symm)
      exact hpq (congrArg Planar.Pattern.prefix (DoubleComb.Vertex.lower.inj he).2)
    | «suffix» c =>
      obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp hy
      have he := congrArg (fun ab : Point n × Point n => ab.1.1) (hle.trans hke.symm)
      exact upperSource_not_lower n c a l he
  | «suffix» a =>
    obtain ⟨k, hk, hke⟩ := Finset.mem_image.mp hx
    cases q with
    | «prefix» c =>
      obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp hy
      have he := congrArg (fun ab : Point n × Point n => ab.1.1) (hke.trans hle.symm)
      exact upperSource_not_lower n a c k he
    | «suffix» c =>
      obtain ⟨l, hl, hle⟩ := Finset.mem_image.mp hy
      have he := congrArg (fun ab : Point n × Point n => ab.2.1.val) (hke.trans hle.symm)
      have hi := congrArg Fin.val (DoubleComb.Vertex.upper.inj he).2
      exact hpq (congrArg Planar.Pattern.suffix (Fin.ext (by dsimp at hi; omega)))


def Private (x : Point n) : Prop := ∃ b : Fin (T + 1), x.1 = branch b

theorem private_moved_exits (b c : Fin (T + 1)) (x : Point n)
    (hx : Private n x) (hb : expandedPerm n b x ≠ x) (hc : expandedPerm n c x ≠ x) : b = c := by
  obtain ⟨d, hd⟩ := hx
  have hb' := (expandedPerm_moves_iff n b x).mp hb
  have hc' := (expandedPerm_moves_iff n c x).mp hc
  rw [hd] at hb' hc'
  exact hb'.2.symm.trans hc'.2

/-- Every moving arc is counted by a proper pattern or touches a private block. -/
theorem shared_arc_cases (hHub : n (hub T) = 0) (b : Fin (T + 1)) (x : Point n)
    (hm : expandedPerm n b x ≠ x) :
    (∃ p : Planar.Pattern T, (x, expandedPerm n b x) ∈ sharedArcs n p) ∨
      Private n x ∨ Private n (expandedPerm n b x) := by
  rcases x with ⟨⟨v, hv⟩, k⟩
  cases v with
  | hub => exact (hv rfl).elim
  | branch i a =>
    cases i
    exact Or.inr (Or.inl ⟨a, rfl⟩)
  | lower i a =>
    cases i
    change expandedPerm n b (⟨prefixBlock a, k⟩ : Point n) ≠ _ at hm
    have hba : b.val ≤ a.val := by
      simpa only [prefixBlock, DoubleComb.OnRoute, true_and] using (expandedPerm_moves_iff n b _).mp hm
    left
    refine ⟨.prefix a, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩⟩
    exact Prod.ext rfl ((lower_arc_occurs_iff n b a k).mpr hba).symm
  | upper i a =>
    cases i
    change expandedPerm n b (⟨up a, k⟩ : Point n) ≠ _ at hm
    have hab : a.val ≤ b.val := by
      simpa only [up, DoubleComb.OnRoute, true_and] using (expandedPerm_moves_iff n b _).mp hm
    have hactive : routePerm b (up a) ≠ up a :=
      (routePerm_moves_iff b _).mpr ⟨rfl, hab⟩
    have hkbound : k.val < n (up a) + 1 := k.isLt
    by_cases hk : k.val < n (up a)
    · rcases Fin.eq_zero_or_eq_succ a with ha | ⟨l, ha⟩
      · subst a
        simp only [up_zero, hHub] at hk
        omega
      · subst a
        have hk' : k.val < n (suffix l) := hk
        left
        refine ⟨.suffix l, Finset.mem_image.mpr ⟨⟨k.val + 1, by omega⟩, Finset.mem_univ _, ?_⟩⟩
        change (upperSource n l ⟨k.val + 1, _⟩, point n (suffix l) (k.val + 1) _) =
          ((⟨suffix l, k⟩ : Point n), expandedPerm n b ⟨suffix l, k⟩)
        apply Prod.ext
        · simp only [upperSource, show ¬k.val + 1 = 0 by omega, dite_eq_right, Nat.add_sub_cancel]
          exact point_ext n rfl rfl
        · exact (lift_apply_next n (routePerm b) (suffix l) k hactive hk).symm
    · have hx : (⟨up a, k⟩ : Point n) = last n (up a) :=
        point_ext n rfl (by dsimp [index]; omega)
      have hstep : expandedPerm n b (⟨up a, k⟩ : Point n) = first n (routePerm b (up a)) := by
        change lift n (routePerm b) _ = _
        rw [hx, lift_apply_last n _ _ hactive]
      by_cases halt : a.val < b.val
      · left
        let l : Fin T := ⟨a.val, by omega⟩
        refine ⟨.suffix l, Finset.mem_image.mpr ⟨0, Finset.mem_univ _, ?_⟩⟩
        apply Prod.ext
        · change last n (up ⟨l.val, _⟩) = (⟨up a, k⟩ : Point n)
          exact hx.symm
        · change first n (suffix l) = expandedPerm n b (⟨up a, k⟩ : Point n)
          rw [hstep, route_up_next b a halt]
          rfl
      · have ha : a = b := Fin.ext (by omega)
        subst a
        right; right
        refine ⟨b, ?_⟩
        change (expandedPerm n b (⟨up b, k⟩ : Point n)).1 = branch b
        rw [hstep, route_up_exit]
        rfl

theorem sharedArcs_private_unique (hHub : n (hub T) = 0)
    (b c : Fin (T + 1)) (x : Point n)
    (hm : expandedPerm n b x ≠ x)
    (hp : ∀ p : Planar.Pattern T, (x, expandedPerm n b x) ∉ sharedArcs n p)
    (heq : expandedPerm n b x = expandedPerm n c x) : b = c := by
  rcases shared_arc_cases n hHub b x hm with ⟨p, h⟩ | h | h
  · exact (hp p h).elim
  · exact private_moved_exits n b c x h hm (fun hf => hm (heq.trans hf))
  · have hn : x ≠ expandedPerm n b x := Ne.symm hm
    have hb := DoubleComb.moved_of_predecessor (expandedPerm n b) rfl hn
    have hc := DoubleComb.moved_of_predecessor (expandedPerm n c) heq.symm hn
    exact private_moved_exits n b c _ h hb hc

end RigidGHZ.Selector.PlanarComb

