module

public import RigidGHZ.Construction.RectanglePatterns
public import Mathlib.Tactic

/-!
# Owner blocks and reusable residual-anchor pools

Every owner is assigned to one full-row, prefix or suffix block. Internal
owners are full-row owners but may supply residual anchors for the two
complementary proper patterns. Such pools are disjoint whenever their
patterns occur in the same cover.
-/

@[expose] public section

namespace RigidGHZ.Rectangle

inductive Pattern (T : ℕ) where
  | full : Pattern T
  | «prefix» (l : Fin T) : Pattern T
  | «suffix» (l : Fin T) : Pattern T
  deriving DecidableEq, Fintype

/-- `suffix l` denotes the interval `[l+1,T]`. -/
def Pattern.occurs {T : ℕ} : Pattern T → ℕ → Prop
  | .full, _ => True
  | .prefix l, b => b ≤ l.val
  | .suffix l, b => l.val < b

/-- Owners assigned to a given loop-omission pattern. -/
def Pattern.owners {T : ℕ} (W J : ℕ) : Pattern T → Finset (ℕ × ℕ)
  | .full => wholeRowOwners W J T
  | .prefix l => prefixOwners W J l.val
  | .suffix l => suffixOwners W J T (l.val + 1)

/-- Internal owners used as anchors outside their own interval of removed tags. -/
def Pattern.residual {T : ℕ} (W J : ℕ) : Pattern T → Finset (ℕ × ℕ)
  | .full => ∅
  | .prefix l => internalStarting W J T l.val
  | .suffix l => internalEnding W J l.val

 theorem prefixOwner_not_last {W J T l : ℕ} (hl : l < T) {x : ℕ × ℕ}
    (hx : x ∈ prefixOwners W J l) : x ∉ rectangle W J T := by
  simp only [prefixOwners, Finset.mem_sdiff, Finset.mem_inter] at hx
  intro hT
  exact hx.2 (rectangle_inter_subset (Nat.zero_le _) (by omega)
    (Finset.mem_inter.mpr ⟨hx.1.1, hT⟩))

 theorem suffixOwner_not_first {W J T l : ℕ} (hl : l < T) {x : ℕ × ℕ}
    (hx : x ∈ suffixOwners W J T (l + 1)) : x ∉ rectangle W J 0 := by
  simp only [suffixOwners, Nat.add_sub_cancel, Finset.mem_sdiff, Finset.mem_inter] at hx
  intro h0
  exact hx.2 (rectangle_inter_subset (Nat.zero_le _) (by omega)
    (Finset.mem_inter.mpr ⟨h0, hx.1.2⟩))

 theorem internalStarting_not_first {W J T l : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ internalStarting W J T l) : x ∉ rectangle W J 0 := by
  simp only [internalStarting, Finset.mem_sdiff] at hx
  intro h0
  exact hx.1.2 (rectangle_inter_subset (Nat.zero_le _) (by omega)
    (Finset.mem_inter.mpr ⟨h0, hx.1.1⟩))

 theorem internalEnding_not_last {W J T l : ℕ} (hl : l < T) {x : ℕ × ℕ}
    (hx : x ∈ internalEnding W J l) : x ∉ rectangle W J T := by
  simp only [internalEnding, Finset.mem_sdiff] at hx
  intro hT
  exact hx.1.2 (rectangle_inter_subset (by omega) (by omega)
    (Finset.mem_inter.mpr ⟨hx.1.1, hT⟩))

/-- Every omitted-tag exit lies in the owner's assigned loop-omission pattern. -/
theorem Pattern.occurs_of_removed {W J T b : ℕ} (p : Pattern T)
    {x : ℕ × ℕ} (hx : x ∈ p.owners W J) (hb : b ≤ T)
    (hxb : x ∈ rectangle W J b) : p.occurs b := by
  cases p with
  | full => trivial
  | «prefix» l =>
    simp only [Pattern.owners, prefixOwners, Finset.mem_sdiff, Finset.mem_inter] at hx
    change b ≤ l.val
    by_contra h
    exact hx.2 (rectangle_inter_subset (Nat.zero_le _) (by omega)
      (Finset.mem_inter.mpr ⟨hx.1.1, hxb⟩))
  | «suffix» l =>
    simp only [Pattern.owners, suffixOwners, Nat.add_sub_cancel,
      Finset.mem_sdiff, Finset.mem_inter] at hx
    change l.val < b
    by_contra h
    exact hx.2 (rectangle_inter_subset (by omega) (Nat.le_of_lt l.isLt)
      (Finset.mem_inter.mpr ⟨hxb, hx.1.2⟩))

/-- A residual anchor's translate is outside the removed rectangle whenever its
assigned complementary pattern occurs. -/
theorem Pattern.residual_avoids {W J T b : ℕ} (p : Pattern T) {x : ℕ × ℕ}
    (hx : x ∈ p.residual W J) (hp : p.occurs b) : x ∉ rectangle W J b := by
  cases p with
  | full => simpa [Pattern.residual] using hx
  | «prefix» l =>
    simp only [Pattern.residual, internalStarting, Finset.mem_sdiff] at hx
    intro hxb
    exact hx.1.2 (rectangle_inter_subset hp (by omega)
      (Finset.mem_inter.mpr ⟨hxb, hx.1.1⟩))
  | «suffix» l =>
    simp only [Pattern.residual, internalEnding, Finset.mem_sdiff] at hx
    intro hxb
    exact hx.1.2 (rectangle_inter_subset (by omega) (by exact hp)
      (Finset.mem_inter.mpr ⟨hx.1.1, hxb⟩))

 theorem Pattern.residual_subset_full {W J T : ℕ} (p : Pattern T) :
    p.residual W J ⊆ (Pattern.full : Pattern T).owners W J := by
  intro x hx
  apply Finset.mem_union_right
  apply Finset.mem_sdiff.mpr
  cases p with
  | full => simpa [Pattern.residual] using hx
  | «prefix» l =>
    have h0 := internalStarting_not_first hx
    simp only [Pattern.residual, internalStarting, Finset.mem_sdiff] at hx
    refine ⟨rectangle_subset_union (Nat.succ_le_of_lt l.isLt) hx.1.1, ?_⟩
    simpa only [Finset.mem_union, not_or] using ⟨h0, hx.2⟩
  | «suffix» l =>
    have hT := internalEnding_not_last l.isLt hx
    simp only [Pattern.residual, internalEnding, Finset.mem_sdiff] at hx
    refine ⟨rectangle_subset_union (Nat.le_of_lt l.isLt) hx.1.1, ?_⟩
    simpa only [Finset.mem_union, not_or] using ⟨hx.2, hT⟩

/-- Pools for two distinct patterns cannot collide when both patterns occur at
one exit. A point may still be reused for the disjoint prefix and suffix outside
its internal interval, exactly as in the paper. -/
theorem Pattern.residual_disjoint_when_used {W J T b : ℕ} (p q : Pattern T)
    (hpq : p ≠ q) (hp : p.occurs b) (hq : q.occurs b) :
    Disjoint (p.residual W J) (q.residual W J) := by
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  cases p with
  | full => simpa [Pattern.residual] using hxp
  | «prefix» l =>
    simp only [Pattern.residual, internalStarting, Finset.mem_sdiff] at hxp
    cases q with
    | full => simpa [Pattern.residual] using hxq
    | «prefix» k =>
      simp only [Pattern.residual, internalStarting, Finset.mem_sdiff] at hxq
      have hlk : l.val ≠ k.val := by intro h; exact hpq (congrArg Pattern.prefix (Fin.ext h))
      rcases lt_or_gt_of_ne hlk with h | h
      · exact hxq.1.2 (rectangle_inter_subset (by omega) (by omega)
          (Finset.mem_inter.mpr ⟨hxp.1.1, hxq.1.1⟩))
      · exact hxp.1.2 (rectangle_inter_subset (by omega) (by omega)
          (Finset.mem_inter.mpr ⟨hxq.1.1, hxp.1.1⟩))
    | «suffix» k =>
      simp only [Pattern.residual, internalEnding, Finset.mem_sdiff] at hxq
      change b ≤ l.val at hp
      change k.val < b at hq
      exact hxp.1.2 (rectangle_inter_subset (by omega) (by omega)
        (Finset.mem_inter.mpr ⟨hxq.1.1, hxp.1.1⟩))
  | «suffix» l =>
    simp only [Pattern.residual, internalEnding, Finset.mem_sdiff] at hxp
    cases q with
    | full => simpa [Pattern.residual] using hxq
    | «prefix» k =>
      simp only [Pattern.residual, internalStarting, Finset.mem_sdiff] at hxq
      change l.val < b at hp
      change b ≤ k.val at hq
      exact hxq.1.2 (rectangle_inter_subset (by omega) (by omega)
        (Finset.mem_inter.mpr ⟨hxp.1.1, hxq.1.1⟩))
    | «suffix» k =>
      simp only [Pattern.residual, internalEnding, Finset.mem_sdiff] at hxq
      have hlk : l.val ≠ k.val := by intro h; exact hpq (congrArg Pattern.suffix (Fin.ext h))
      rcases lt_or_gt_of_ne hlk with h | h
      · exact hxp.1.2 (rectangle_inter_subset (by omega) (by omega)
          (Finset.mem_inter.mpr ⟨hxp.1.1, hxq.1.1⟩))
      · exact hxq.1.2 (rectangle_inter_subset (by omega) (by omega)
          (Finset.mem_inter.mpr ⟨hxq.1.1, hxp.1.1⟩))

 theorem mem_suffixOwners_iff {W J T l : ℕ} (hl : l < T) (x : ℕ × ℕ) :
    x ∈ suffixOwners W J T (l + 1) ↔ exits W J T x = Finset.Ico (l + 1) (T + 1) := by
  simp only [suffixOwners, Nat.add_sub_cancel, Finset.mem_sdiff, Finset.mem_inter]
  constructor
  · rintro ⟨⟨hxl, hxT⟩, hxn⟩
    ext b
    simp only [exits, Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨hb, hxb⟩
      refine ⟨?_, hb⟩
      by_contra h
      exact hxn (rectangle_inter_subset (by omega) (by omega)
        (Finset.mem_inter.mpr ⟨hxb, hxT⟩))
    · rintro ⟨hb, hbT⟩
      exact ⟨hbT, rectangle_inter_subset hb (by omega) (Finset.mem_inter.mpr ⟨hxl, hxT⟩)⟩
  · intro he
    have hl' : l + 1 ∈ exits W J T x := by rw [he]; simp; omega
    have hT : T ∈ exits W J T x := by rw [he]; simp; omega
    have hn : l ∉ exits W J T x := by rw [he]; simp
    simp only [exits, Finset.mem_filter, Finset.mem_range] at hl' hT hn
    exact ⟨⟨hl'.2, hT.2⟩, fun h => hn ⟨by omega, h⟩⟩

 theorem Pattern.owners_disjoint {W J T : ℕ} :
    Pairwise (fun p q : Pattern T => Disjoint (p.owners W J) (q.owners W J)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  cases p with
  | full =>
    simp only [Pattern.owners, wholeRowOwners, Finset.mem_union,
      Finset.mem_inter, Finset.mem_sdiff, not_or] at hxp
    cases q with
    | full => exact hpq rfl
    | «prefix» k =>
      have hnT := prefixOwner_not_last k.isLt hxq
      have h0 : x ∈ rectangle W J 0 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxq).1).1
      rcases hxp with hh | hh
      · exact hnT hh.2
      · exact hh.2.1 h0
    | «suffix» k =>
      have hn0 := suffixOwner_not_first k.isLt hxq
      have hT : x ∈ rectangle W J T := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxq).1).2
      rcases hxp with hh | hh
      · exact hn0 hh.1
      · exact hh.2.2 hT
  | «prefix» l =>
    have hnT := prefixOwner_not_last l.isLt hxp
    have h0 : x ∈ rectangle W J 0 := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxp).1).1
    cases q with
    | full =>
      simp only [Pattern.owners, wholeRowOwners, Finset.mem_union,
        Finset.mem_inter, Finset.mem_sdiff, not_or] at hxq
      rcases hxq with hh | hh
      · exact hnT hh.2
      · exact hh.2.1 h0
    | «prefix» k =>
      have he := ((mem_prefixOwners_iff l.isLt x).mp hxp).symm.trans
        ((mem_prefixOwners_iff k.isLt x).mp hxq)
      have hc := congrArg Finset.card he
      simp only [Finset.card_range] at hc
      exact hpq (congrArg Pattern.prefix (Fin.ext (by omega)))
    | «suffix» k => exact (suffixOwner_not_first k.isLt hxq) h0
  | «suffix» l =>
    have hn0 := suffixOwner_not_first l.isLt hxp
    have hT : x ∈ rectangle W J T := (Finset.mem_inter.mp (Finset.mem_sdiff.mp hxp).1).2
    cases q with
    | full =>
      simp only [Pattern.owners, wholeRowOwners, Finset.mem_union,
        Finset.mem_inter, Finset.mem_sdiff, not_or] at hxq
      rcases hxq with hh | hh
      · exact hn0 hh.1
      · exact hh.2.2 hT
    | «prefix» k => exact (prefixOwner_not_last k.isLt hxq) hT
    | «suffix» k =>
      have he := ((mem_suffixOwners_iff l.isLt x).mp hxp).symm.trans
        ((mem_suffixOwners_iff k.isLt x).mp hxq)
      have hc := congrArg Finset.card he
      simp only [Nat.card_Ico] at hc
      exact hpq (congrArg Pattern.suffix (Fin.ext (by omega)))

 theorem Pattern.owners_subset_union {W J T : ℕ} (p : Pattern T) :
    p.owners W J ⊆ rectangleUnion W J T := by
  intro x hx
  cases p with
  | full =>
    simp only [Pattern.owners, wholeRowOwners, Finset.mem_union,
      Finset.mem_inter, Finset.mem_sdiff] at hx
    rcases hx with h | h
    · exact rectangle_subset_union (Nat.zero_le _) h.1
    · exact h.1
  | «prefix» l =>
    exact rectangle_subset_union (Nat.zero_le _) (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).1
  | «suffix» l =>
    exact rectangle_subset_union le_rfl (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2

/-- The owner blocks really partition every rectangle's owners, including full
and internal intervals, and each owner has exactly one block. -/
theorem owner_pattern_unique {W J T : ℕ} {x : ℕ × ℕ}
    (hx : x ∈ rectangleUnion W J T) : ∃! p : Pattern T, x ∈ p.owners W J := by
  have hex : ∃ p : Pattern T, x ∈ p.owners W J := by
    have hS : (exits W J T x).Nonempty := by
      obtain ⟨b, hb, hxb⟩ := Finset.mem_biUnion.mp hx
      exact ⟨b, Finset.mem_filter.mpr ⟨hb, hxb⟩⟩
    by_cases h0 : x ∈ rectangle W J 0
    · by_cases hT : x ∈ rectangle W J T
      · exact ⟨.full, Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h0, hT⟩)⟩
      · let l := (exits W J T x).max' hS
        have hlmem : l ∈ exits W J T x := Finset.max'_mem _ hS
        have hl := Finset.mem_filter.mp hlmem
        have hlT : l < T := by
          have hlbound := Finset.mem_range.mp hl.1
          have hlne : l ≠ T := by intro h; exact hT (h ▸ hl.2)
          omega
        have hn : x ∉ rectangle W J (l + 1) := by
          intro hh
          have hnmem : l + 1 ∈ exits W J T x :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩
          have hnle := Finset.le_max' (exits W J T x) (l + 1) hnmem
          change l + 1 ≤ l at hnle
          omega
        exact ⟨.prefix ⟨l, hlT⟩, Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h0, hl.2⟩, hn⟩⟩
    · by_cases hT : x ∈ rectangle W J T
      · let j := (exits W J T x).min' hS
        have hjmem : j ∈ exits W J T x := Finset.min'_mem _ hS
        have hj := Finset.mem_filter.mp hjmem
        have hjpos : 0 < j := by
          have hjne : j ≠ 0 := by intro h; exact h0 (h ▸ hj.2)
          omega
        have hjT : j ≤ T := by have := Finset.mem_range.mp hj.1; omega
        have hn : x ∉ rectangle W J (j - 1) := by
          intro hh
          have hnmem : j - 1 ∈ exits W J T x :=
            Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hh⟩
          have hnle := Finset.min'_le (exits W J T x) (j - 1) hnmem
          change j ≤ j - 1 at hnle
          omega
        refine ⟨.suffix ⟨j - 1, by omega⟩, ?_⟩
        change x ∈ suffixOwners W J T (j - 1 + 1)
        rw [show j - 1 + 1 = j by omega]
        exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨hj.2, hT⟩, hn⟩
      · exact ⟨.full, Finset.mem_union_right _
          (Finset.mem_sdiff.mpr ⟨hx, by simpa only [Finset.mem_union, not_or] using ⟨h0, hT⟩⟩)⟩
  obtain ⟨p, hp⟩ := hex
  refine ⟨p, hp, ?_⟩
  intro q hq
  by_contra hqp
  exact Finset.disjoint_left.mp (Pattern.owners_disjoint (W := W) (J := J) hqp) hq hp

 theorem proper_owner_nonempty {W J T : ℕ} (hW : T ≤ W) (hJ : gamma T < J)
    (l : Fin T) : ((Pattern.prefix l).owners W J).Nonempty ∧
      ((Pattern.suffix l).owners W J).Nonempty := by
  have hp := prefix_net_demand l.isLt hW (Nat.le_of_lt hJ)
  have hs := suffix_net_demand l.isLt hW (Nat.le_of_lt hJ)
  constructor <;> apply Finset.card_pos.mp <;> dsimp [Pattern.owners] <;> omega

 theorem full_owner_nonempty {W J T : ℕ} (hT : 1 ≤ T) (hW : T < W)
    (hJ : gamma T < J) : ((Pattern.full : Pattern T).owners W J).Nonempty := by
  apply Finset.card_pos.mp
  change 0 < (wholeRowOwners W J T).card
  rw [wholeRow_card hT (Nat.le_of_lt hW) (Nat.le_of_lt hJ)]
  have hp : 0 < (W - T) * (J - gamma T) := Nat.mul_pos (by omega) (by omega)
  omega

end RigidGHZ.Rectangle
