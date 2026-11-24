module

public import RigidGHZ.Partite
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Data.Finset.Max

@[expose] public section

namespace RigidGHZ.Selector

/-- A permutation following a specified cycle and an acyclic graph away from its hub
has no additional nontrivial cycles. This also handles vertices unused by every route. -/
theorem eq_viaEmbedding_of_acyclic_complement
    {V K : Type*} [Fintype V] [DecidableEq V]
    (r : K ↪ V) (c : Equiv.Perm K) (q : Equiv.Perm V)
    (hub : V) (hhub : hub ∈ Set.range r) (rank : V → ℕ)
    (hincrease : ∀ x, x ≠ hub → q x ≠ hub → q x ≠ x → rank x < rank (q x))
    (hroute : ∀ k, q (r k) = r (c k)) :
    q = c.viaEmbedding r := by
  classical
  have hout : ∀ x, x ∉ Set.range r → q x ∉ Set.range r := by
    intro x hx hqx
    obtain ⟨k, hk⟩ := hqx
    have heq : q (r (c.symm k)) = q x :=
      (hroute (c.symm k)).trans ((congrArg r (c.apply_symm_apply k)).trans hk)
    exact hx ⟨c.symm k, q.injective heq⟩
  have hfix : ∀ x, x ∉ Set.range r → q x = x := by
    intro x hx
    by_contra hne
    let S : Finset V := Finset.univ.filter (fun v => v ∉ Set.range r ∧ q v ≠ v)
    have hxS : x ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hne⟩
    obtain ⟨y, hy, hmax⟩ := S.exists_max_image rank ⟨x, hxS⟩
    have hy' : y ∉ Set.range r ∧ q y ≠ y := by simpa [S] using hy
    have hqy : q y ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hout y hy'.1, fun h => hy'.2 (q.injective h)⟩
    have hyhub : y ≠ hub := fun h => hy'.1 (h ▸ hhub)
    have hqyhub : q y ≠ hub := fun h => hout y hy'.1 (h ▸ hhub)
    exact (not_lt_of_ge (hmax (q y) hqy)) (hincrease y hyhub hqyhub hy'.2)
  ext x
  by_cases hx : x ∈ Set.range r
  · obtain ⟨k, rfl⟩ := hx
    rw [Equiv.Perm.viaEmbedding_apply, hroute]
  · rw [Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx, hfix x hx]

namespace DoubleComb

/-- A compressed double comb: the zeroth upper block represents the full-row chain;
positive upper blocks are suffix chains, and lower blocks are prefix chains. -/
inductive Vertex (R : Type*) (T : ℕ) where
  | hub : Vertex R T
  | upper (row : R) (exit : Fin (T + 1)) : Vertex R T
  | branch (row : R) (exit : Fin (T + 1)) : Vertex R T
  | lower (row : R) (exit : Fin T) : Vertex R T
  deriving DecidableEq, Fintype

open Vertex

variable {R : Type*} {T : ℕ}

/-- Exactly the loop and route arcs of the compressed double comb. There is no hub loop. -/
def Arc : Vertex R T → Vertex R T → Prop
  | hub, y => ∃ i, y = upper i 0
  | upper i a, y => y = upper i a ∨ y = branch i a ∨
      ∃ h : a.val < T, y = upper i ⟨a.val + 1, by omega⟩
  | branch i b, y => y = branch i b ∨
      if h : b.val < T then y = lower i ⟨b.val, h⟩ else y = hub
  | lower i a, y => y = lower i a ∨
      if h : a.val + 1 < T then y = lower i ⟨a.val + 1, h⟩ else y = hub

/-- A cycle cover is an ordinary permutation whose arrows belong to `Arc`. -/
def Cover (q : Equiv.Perm (Vertex R T)) : Prop := ∀ v, Arc v (q v)

/-- A topological rank after removing the hub and loops. -/
def rank : Vertex R T → ℕ
  | hub => 0
  | upper _ a => a.val
  | branch _ b => T + 1 + b.val
  | lower _ a => 2 * T + 2 + a.val

 theorem rank_increases {x y : Vertex R T} (h : Arc x y)
    (hx : x ≠ hub) (hy : y ≠ hub) (hne : y ≠ x) : rank x < rank y := by
  cases x with
  | hub => exact (hx rfl).elim
  | upper i a =>
    rcases h with h | h | ⟨ha, h⟩
    · exact (hne h).elim
    · subst y; simp only [rank]; omega
    · subst y; simp only [rank]; omega
  | branch i b =>
    rcases h with h | h
    · exact (hne h).elim
    · split_ifs at h with hb
      · subst y; simp only [rank]; omega
      · exact (hy h).elim
  | lower i a =>
    rcases h with h | h
    · exact (hne h).elim
    · split_ifs at h with ha
      · subst y; simp only [rank]; omega
      · exact (hy h).elim

/-- The successive vertices of route `(i,b)`. Each compressed route has `T+3` vertices. -/
def routeAt (i : R) (b : Fin (T + 1)) (k : Fin (T + 3)) : Vertex R T :=
  if h0 : k.val = 0 then hub
  else if hu : k.val ≤ b.val + 1 then upper i ⟨k.val - 1, by omega⟩
  else if hp : k.val = b.val + 2 then branch i b
  else lower i ⟨k.val - 3, by omega⟩

@[simp] theorem routeAt_zero (i : R) (b : Fin (T + 1)) : routeAt i b 0 = hub := by
  simp [routeAt]

 theorem routeAt_injective (i : R) (b : Fin (T + 1)) : Function.Injective (routeAt i b) := by
  intro k l h
  dsimp [routeAt] at h
  split_ifs at h <;> simp only [Vertex.upper.injEq, Vertex.branch.injEq,
    Vertex.lower.injEq, Fin.mk.injEq, true_and] at h <;>
    try contradiction
  all_goals apply Fin.ext; omega

/-- Embed a selected route into all double-comb vertices. -/
def routeEmbedding (i : R) (b : Fin (T + 1)) : Fin (T + 3) ↪ Vertex R T :=
  ⟨routeAt i b, routeAt_injective i b⟩

/-- The intended cycle cover traverses one route and fixes every other vertex. -/
noncomputable def routePerm (i : R) (b : Fin (T + 1)) : Equiv.Perm (Vertex R T) :=
  (finRotate (T + 3)).viaEmbedding (routeEmbedding i b)

@[simp] theorem routePerm_apply_routeAt (i : R) (b : Fin (T + 1)) (k : Fin (T + 3)) :
    routePerm i b (routeAt i b k) = routeAt i b (finRotate (T + 3) k) := by
  exact Equiv.Perm.viaEmbedding_apply _ _ _

 theorem routePerm_apply_of_notMem (i : R) (b : Fin (T + 1)) (x : Vertex R T)
    (hx : x ∉ Set.range (routeAt i b)) : routePerm i b x = x := by
  exact Equiv.Perm.viaEmbedding_apply_of_notMem _ _ _ hx

@[simp] theorem routeAt_upper (i : R) (b a : Fin (T + 1)) (ha : a.val ≤ b.val) :
    routeAt i b ⟨a.val + 1, by omega⟩ = upper i a := by
  simp [routeAt, ha, Nat.add_le_add_iff_right]

@[simp] theorem routeAt_branch (i : R) (b : Fin (T + 1)) :
    routeAt i b ⟨b.val + 2, by omega⟩ = branch i b := by
  simp [routeAt]

@[simp] theorem routeAt_lower (i : R) (b : Fin (T + 1)) (a : Fin T)
    (ha : b.val ≤ a.val) :
    routeAt i b ⟨a.val + 3, by omega⟩ = lower i a := by
  simp [routeAt, show ¬a.val + 3 ≤ b.val + 1 by omega,
    show ¬a.val + 3 = b.val + 2 by omega]

set_option maxRecDepth 4096 in
 theorem arc_routeAt (i : R) (b : Fin (T + 1)) (k : Fin (T + 3)) :
    Arc (routeAt i b k) (routeAt i b (finRotate (T + 3) k)) := by
  rcases k with ⟨k, hk⟩
  by_cases hlast : k = T + 2
  · subst k
    rw [finRotate_last']
    unfold routeAt
    simp only [Fin.val_mk]
    split_ifs <;> simp_all [Arc] <;> omega
  · have hk' : k < T + 2 := by omega
    rw [finRotate_of_lt hk']
    unfold routeAt
    simp only [Fin.val_mk]
    split_ifs <;> simp_all [Arc] <;> omega

 theorem routePerm_cover (i : R) (b : Fin (T + 1)) : Cover (routePerm i b) := by
  intro x
  by_cases hx : x ∈ Set.range (routeAt i b)
  · obtain ⟨k, rfl⟩ := hx
    rw [routePerm_apply_routeAt]
    exact arc_routeAt i b k
  · rw [routePerm_apply_of_notMem i b x hx]
    cases x with
    | hub => exact (hx ⟨0, routeAt_zero i b⟩).elim
    | upper j a => exact Or.inl rfl
    | branch j a => exact Or.inl rfl
    | lower j a => exact Or.inl rfl

/-- The next route vertex before adding the loops outside that route. -/
def step (i : R) (b : Fin (T + 1)) : Vertex R T → Vertex R T
  | hub => upper i 0
  | upper j a => if h : a.val < b.val then upper j ⟨a.val + 1, by omega⟩ else branch j a
  | branch j a => if h : a.val < T then lower j ⟨a.val, h⟩ else hub
  | lower j a => if h : a.val + 1 < T then lower j ⟨a.val + 1, h⟩ else hub

/-- Vertices on a selected route. -/
def OnRoute (i : R) (b : Fin (T + 1)) : Vertex R T → Prop
  | hub => True
  | upper j a => j = i ∧ a.val ≤ b.val
  | branch j a => j = i ∧ a = b
  | lower j a => j = i ∧ b.val ≤ a.val

 theorem routeAt_onRoute (i : R) (b : Fin (T + 1)) (k : Fin (T + 3)) :
    OnRoute i b (routeAt i b k) := by
  unfold routeAt
  split_ifs <;> simp only [OnRoute, true_and] <;> omega

set_option maxRecDepth 4096 in
 theorem step_routeAt (i : R) (b : Fin (T + 1)) (k : Fin (T + 3)) :
    step i b (routeAt i b k) = routeAt i b (finRotate (T + 3) k) := by
  rcases k with ⟨k, hk⟩
  by_cases hlast : k = T + 2
  · subst k
    rw [finRotate_last']
    unfold routeAt
    simp only [Fin.val_mk]
    split_ifs <;> simp_all [step] <;> (try split_ifs) <;> simp_all <;> omega
  · have hk' : k < T + 2 := by omega
    rw [finRotate_of_lt hk']
    unfold routeAt
    simp only [Fin.val_mk]
    split_ifs <;> simp_all [step] <;> (try split_ifs) <;> simp_all <;> omega

 theorem moved_of_predecessor {V : Type*} (q : Equiv.Perm V) {x y : V}
    (h : q x = y) (hne : x ≠ y) : q y ≠ y := by
  intro hfix
  exact hne (q.injective (h.trans hfix.symm))

/-- Starting along an upper tooth forces a unique first private block. -/
theorem exists_exit_from (q : Equiv.Perm (Vertex R T)) (hq : Cover q)
    (i : R) (a : Fin (T + 1)) (hmoved : q (upper i a) ≠ upper i a) :
    ∃ b : Fin (T + 1), a.val ≤ b.val ∧ q (upper i b) = branch i b ∧
      ∀ (c : Fin (T + 1)) (_hac : a.val ≤ c.val) (hcb : c.val < b.val),
        q (upper i c) = upper i ⟨c.val + 1, by omega⟩ := by
  suffices ∀ n : ℕ, ∀ a : Fin (T + 1), T - a.val = n →
      q (upper i a) ≠ upper i a →
      ∃ b : Fin (T + 1), a.val ≤ b.val ∧ q (upper i b) = branch i b ∧
        ∀ (c : Fin (T + 1)) (_hac : a.val ≤ c.val) (hcb : c.val < b.val),
          q (upper i c) = upper i ⟨c.val + 1, by omega⟩ by
    exact this (T - a.val) a rfl hmoved
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro a han hmove
    rcases hq (upper i a) with hloop | hexit | ⟨hanext, hnext⟩
    · exact (hmove hloop).elim
    · refine ⟨a, le_rfl, hexit, ?_⟩
      intro c hac hca
      omega
    · let a' : Fin (T + 1) := ⟨a.val + 1, by omega⟩
      have hm' : q (upper i a') ≠ upper i a' :=
        moved_of_predecessor q hnext (by simp [a', Fin.ext_iff])
      obtain ⟨b, hab, hb, hpath⟩ := ih (T - a'.val) (by dsimp [a']; omega) a' rfl hm'
      refine ⟨b, by dsimp [a'] at hab; omega, hb, ?_⟩
      intro c hac hcb
      by_cases hca : c = a
      · subst c; exact hnext
      · apply hpath c
        · dsimp [a']; have : c.val ≠ a.val := fun h => hca (Fin.ext h); omega
        · exact hcb

/-- A private block forces the entire following lower tooth. -/
theorem lower_follows (q : Equiv.Perm (Vertex R T)) (hq : Cover q)
    (i : R) (b : Fin (T + 1)) (hexit : q (upper i b) = branch i b) :
    q (branch i b) = step i b (branch i b) ∧
    ∀ a : Fin T, b.val ≤ a.val → q (lower i a) = step i b (lower i a) := by
  have hmbranch : q (branch i b) ≠ branch i b :=
    moved_of_predecessor q hexit (by simp)
  have hbranch : q (branch i b) = step i b (branch i b) := by
    dsimp [step]
    split_ifs with h
    · simpa [h] using (hq (branch i b)).resolve_left hmbranch
    · simpa [h] using (hq (branch i b)).resolve_left hmbranch
  refine ⟨hbranch, ?_⟩
  have hmoved : ∀ n : ℕ, ∀ hn : n < T, b.val ≤ n →
      q (lower i ⟨n, hn⟩) ≠ lower i ⟨n, hn⟩ := by
    intro n
    induction n with
    | zero =>
      intro hn hb
      have hb0 : b.val = 0 := by omega
      have hpred : q (branch i b) = lower i ⟨0, hn⟩ := by
        simpa [step, hb0, hn] using hbranch
      exact moved_of_predecessor q hpred (by simp)
    | succ n ih =>
      intro hn hb
      by_cases hbn : b.val = n + 1
      · have hpred : q (branch i b) = lower i ⟨n + 1, hn⟩ := by
          simpa [step, hbn, hn] using hbranch
        exact moved_of_predecessor q hpred (by simp)
      · have hprev : q (lower i ⟨n, by omega⟩) ≠ lower i ⟨n, by omega⟩ :=
          ih (by omega) (by omega)
        have hpred : q (lower i ⟨n, by omega⟩) = lower i ⟨n + 1, hn⟩ := by
          have hh := (hq (lower i ⟨n, by omega⟩)).resolve_left hprev
          simpa [Arc, hn] using hh
        exact moved_of_predecessor q hpred (by simp [Fin.ext_iff])
  intro a ha
  dsimp [step]
  split_ifs with h
  · simpa [h] using (hq (lower i a)).resolve_left (hmoved a.val a.isLt ha)
  · simpa [h] using (hq (lower i a)).resolve_left (hmoved a.val a.isLt ha)

/-- Every cycle cover of the actual compressed double comb is one prescribed route. -/
theorem cover_complete [Fintype R] [DecidableEq R]
    (q : Equiv.Perm (Vertex R T)) (hq : Cover q) :
    ∃ i : R, ∃ b : Fin (T + 1), q = routePerm i b := by
  obtain ⟨i, hhub⟩ := hq hub
  have hstart : q (upper i 0) ≠ upper i 0 :=
    moved_of_predecessor q hhub (by simp)
  obtain ⟨b, _, hexit, hupper⟩ := exists_exit_from q hq i 0 hstart
  obtain ⟨hbranch, hlower⟩ := lower_follows q hq i b hexit
  have hagree : ∀ x, OnRoute i b x → q x = step i b x := by
    intro x hx
    cases x with
    | hub => exact hhub
    | upper j a =>
      obtain ⟨rfl, hab⟩ := hx
      by_cases hlt : a.val < b.val
      · simpa [step, hlt] using hupper a (by simp) hlt
      · have hab' : a = b := Fin.ext (by omega)
        subst a
        simpa [step] using hexit
    | branch j a =>
      obtain ⟨rfl, rfl⟩ := hx
      exact hbranch
    | lower j a =>
      obtain ⟨rfl, hab⟩ := hx
      exact hlower a hab
  refine ⟨i, b, ?_⟩
  apply eq_viaEmbedding_of_acyclic_complement (routeEmbedding i b) (finRotate (T + 3)) q
    hub ⟨0, routeAt_zero i b⟩ rank
  · intro x hx hqx hne
    exact rank_increases (hq x) hx hqx hne
  · intro k
    exact (hagree (routeAt i b k) (routeAt_onRoute i b k)).trans (step_routeAt i b k)

 theorem onRoute_iff_range (i : R) (b : Fin (T + 1)) (x : Vertex R T) :
    OnRoute i b x ↔ x ∈ Set.range (routeAt i b) := by
  constructor
  · intro hx
    cases x with
    | hub => exact ⟨0, routeAt_zero i b⟩
    | upper j a =>
      obtain ⟨hji, hab⟩ := hx
      subst j
      exact ⟨⟨a.val + 1, by omega⟩, routeAt_upper i b a hab⟩
    | branch j a =>
      obtain ⟨hji, hab⟩ := hx
      subst j a
      exact ⟨⟨b.val + 2, by omega⟩, routeAt_branch i b⟩
    | lower j a =>
      obtain ⟨hji, hba⟩ := hx
      subst j
      exact ⟨⟨a.val + 3, by omega⟩, routeAt_lower i b a hba⟩
  · rintro ⟨k, rfl⟩
    exact routeAt_onRoute i b k

 theorem routePerm_apply_onRoute (i : R) (b : Fin (T + 1)) (x : Vertex R T)
    (hx : OnRoute i b x) : routePerm i b x = step i b x := by
  obtain ⟨k, rfl⟩ := (onRoute_iff_range i b x).mp hx
  rw [routePerm_apply_routeAt, step_routeAt]

 theorem step_ne_self (i : R) (b : Fin (T + 1)) (x : Vertex R T) :
    step i b x ≠ x := by
  cases x <;> simp only [step] <;> (try split_ifs) <;> simp [Fin.ext_iff]

 theorem routePerm_moves_iff (i : R) (b : Fin (T + 1)) (x : Vertex R T) :
    routePerm i b x ≠ x ↔ OnRoute i b x := by
  by_cases hx : OnRoute i b x
  · rw [routePerm_apply_onRoute i b x hx]
    exact iff_of_true (step_ne_self i b x) hx
  · have hx' : x ∉ Set.range (routeAt i b) := mt (onRoute_iff_range i b x).mpr hx
    rw [routePerm_apply_of_notMem i b x hx']
    simp [hx]

 theorem routePerm_injective :
    Function.Injective (fun ib : R × Fin (T + 1) => routePerm ib.1 ib.2) := by
  rintro ⟨i, b⟩ ⟨j, c⟩ h
  change routePerm i b = routePerm j c at h
  have hm : routePerm i b (branch i b) ≠ branch i b :=
    (routePerm_moves_iff i b _).mpr ⟨rfl, rfl⟩
  rw [h] at hm
  have hc := (routePerm_moves_iff j c _).mp hm
  exact Prod.ext hc.1 hc.2

 theorem cover_iff [Fintype R] [DecidableEq R] (q : Equiv.Perm (Vertex R T)) :
    Cover q ↔ ∃ i : R, ∃ b : Fin (T + 1), q = routePerm i b := by
  constructor
  · exact cover_complete q
  · rintro ⟨i, b, rfl⟩
    exact routePerm_cover i b

end DoubleComb
end RigidGHZ.Selector
