module

public import RigidGHZ.Construction.PlanarHoles
public import Mathlib.Data.Finset.Max
public import Mathlib.Tactic.DeriveFintype

/-! Proper interval owner patterns and the two complementary enlargement rules. -/

@[expose] public section

namespace RigidGHZ.Planar

open scoped Finset

inductive Pattern (T : ℕ) where
  | «prefix» (l : Fin T)
  | «suffix» (l : Fin T)
  deriving DecidableEq, Fintype

def Pattern.occurs {T : ℕ} : Pattern T → ℕ → Prop
  | .prefix l, b => b ≤ l.val
  | .suffix l, b => l.val < b

variable {X : Type*} [DecidableEq X] {T : ℕ}

def IntervalFamily (F : ℕ → Finset X) : Prop :=
  ∀ ⦃a b c : ℕ⦄, a ≤ b → b ≤ c → ∀ ⦃x : X⦄, x ∈ F a → x ∈ F c → x ∈ F b

def ending (F : ℕ → Finset X) (l : ℕ) := F l \ F (l + 1)
def starting (F : ℕ → Finset X) (l : ℕ) := F (l + 1) \ F l

def leftOwners (F : ℕ → Finset X) : Pattern T → Finset X
  | .prefix l => ending F l.val
  | .suffix l => (F (l.val + 1) ∩ F T) \ F l.val

def rightOwners (F : ℕ → Finset X) : Pattern T → Finset X
  | .prefix l => (F 0 ∩ F l.val) \ F (l.val + 1)
  | .suffix l => starting F l.val

def leftResidual (F : ℕ → Finset X) : Pattern T → Finset X
  | .prefix l => starting F l.val \ F T
  | .suffix _ => ∅

def rightResidual (F : ℕ → Finset X) : Pattern T → Finset X
  | .prefix _ => ∅
  | .suffix l => ending F l.val \ F 0

theorem ending_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun l k => Disjoint (ending F l) (ending F k)) := by
  intro l k hlk
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [ending, Finset.mem_sdiff] at hx hy
  rcases lt_or_gt_of_ne hlk with hlk | hkl
  · exact hx.2 (hF (by omega) (by omega) hx.1 hy.1)
  · exact hy.2 (hF (by omega) (by omega) hy.1 hx.1)

theorem starting_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun l k => Disjoint (starting F l) (starting F k)) := by
  intro l k hlk
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [starting, Finset.mem_sdiff] at hx hy
  rcases lt_or_gt_of_ne hlk with hlk | hkl
  · exact hy.2 (hF (by omega) (by omega) hx.1 hy.1)
  · exact hx.2 (hF (by omega) (by omega) hy.1 hx.1)

theorem ending_not_last {F : ℕ → Finset X} (hF : IntervalFamily F)
    {l : Fin T} {x : X} (hx : x ∈ ending F l.val) : x ∉ F T := by
  simp only [ending, Finset.mem_sdiff] at hx
  intro hT
  exact hx.2 (hF (by omega) (by omega) hx.1 hT)

theorem starting_not_first {F : ℕ → Finset X} (hF : IntervalFamily F)
    {l : ℕ} {x : X} (hx : x ∈ starting F l) : x ∉ F 0 := by
  simp only [starting, Finset.mem_sdiff] at hx
  intro h0
  exact hx.2 (hF (Nat.zero_le _) (by omega) h0 hx.1)

theorem leftOwners_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun p q : Pattern T => Disjoint (leftOwners F p) (leftOwners F q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  cases p with
  | «prefix» l =>
    cases q with
    | «prefix» k =>
      exact Finset.disjoint_left.mp (ending_disjoint F hF
        (fun he => hpq (congrArg Pattern.prefix (Fin.ext he)))) hx hy
    | «suffix» k => exact ending_not_last hF hx (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2
  | «suffix» l =>
    cases q with
    | «prefix» k => exact ending_not_last hF hy (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2
    | «suffix» k =>
      apply Finset.disjoint_left.mp (starting_disjoint F hF
        (fun he => hpq (congrArg Pattern.suffix (Fin.ext he))))
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).1,
          (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).1,
          (Finset.mem_sdiff.mp hy).2⟩

theorem rightOwners_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun p q : Pattern T => Disjoint (rightOwners F p) (rightOwners F q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  cases p with
  | «prefix» l =>
    cases q with
    | «prefix» k =>
      apply Finset.disjoint_left.mp (ending_disjoint F hF
        (fun he => hpq (congrArg Pattern.prefix (Fin.ext he))))
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2,
          (Finset.mem_sdiff.mp hx).2⟩
      · exact Finset.mem_sdiff.mpr ⟨(Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2,
          (Finset.mem_sdiff.mp hy).2⟩
    | «suffix» k => exact starting_not_first hF hy (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).1
  | «suffix» l =>
    cases q with
    | «prefix» k => exact starting_not_first hF hx (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).1
    | «suffix» k =>
      exact Finset.disjoint_left.mp (starting_disjoint F hF
        (fun he => hpq (congrArg Pattern.suffix (Fin.ext he)))) hx hy

theorem exists_ending {F : ℕ → Finset X} {x : X}
    (hx : ∃ b ≤ T, x ∈ F b) (hn : x ∉ F T) :
    ∃ l : Fin T, x ∈ ending F l.val := by
  let s := (Finset.range (T + 1)).filter (fun b => x ∈ F b)
  have hs : s.Nonempty := by
    obtain ⟨b, hb, hx⟩ := hx
    exact ⟨b, by simp only [s, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hx⟩⟩
  obtain ⟨l, hl, hmax⟩ := s.exists_max_image id hs
  have hls : l < T + 1 ∧ x ∈ F l := by simpa [s] using hl
  have hlT : l < T := by
    by_contra hn'
    have he : l = T := by omega
    exact hn (he ▸ hls.2)
  refine ⟨⟨l, hlT⟩, Finset.mem_sdiff.mpr ⟨hls.2, ?_⟩⟩
  intro hnext
  have hnmem : l + 1 ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hnext⟩
  have hle := hmax (l + 1) hnmem
  dsimp at hle
  omega

theorem exists_starting {F : ℕ → Finset X} {x : X}
    (hx : ∃ b ≤ T, x ∈ F b) (hn : x ∉ F 0) :
    ∃ l : Fin T, x ∈ starting F l.val := by
  let s := (Finset.range (T + 1)).filter (fun b => x ∈ F b)
  have hs : s.Nonempty := by
    obtain ⟨b, hb, hx⟩ := hx
    exact ⟨b, by simp only [s, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hx⟩⟩
  obtain ⟨j, hj, hmin⟩ := s.exists_min_image id hs
  have hjs : j < T + 1 ∧ x ∈ F j := by simpa [s] using hj
  have hj0 : 0 < j := by
    by_contra hn'
    have he : j = 0 := by omega
    exact hn (he ▸ hjs.2)
  refine ⟨⟨j - 1, by omega⟩, Finset.mem_sdiff.mpr ⟨?_, ?_⟩⟩
  · simpa only [show j - 1 + 1 = j by omega] using hjs.2
  · intro hprev
    have hnmem : j - 1 ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_range]; exact ⟨by omega, hprev⟩
    have hle := hmin (j - 1) hnmem
    dsimp at hle
    omega

theorem leftOwners_cover {F : ℕ → Finset X} (hp : Disjoint (F 0) (F T))
    {x : X} (hx : ∃ b ≤ T, x ∈ F b) : ∃ p : Pattern T, x ∈ leftOwners F p := by
  by_cases hT : x ∈ F T
  · obtain ⟨l, hl⟩ := exists_starting hx (fun h0 => Finset.disjoint_left.mp hp h0 hT)
    refine ⟨.suffix l, ?_⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hl).1, hT⟩,
      (Finset.mem_sdiff.mp hl).2⟩
  · obtain ⟨l, hl⟩ := exists_ending hx hT
    exact ⟨.prefix l, hl⟩

theorem rightOwners_cover {F : ℕ → Finset X} (hp : Disjoint (F 0) (F T))
    {x : X} (hx : ∃ b ≤ T, x ∈ F b) : ∃ p : Pattern T, x ∈ rightOwners F p := by
  by_cases h0 : x ∈ F 0
  · obtain ⟨l, hl⟩ := exists_ending hx (fun hT => Finset.disjoint_left.mp hp h0 hT)
    refine ⟨.prefix l, ?_⟩
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_inter.mpr ⟨h0, (Finset.mem_sdiff.mp hl).1⟩,
      (Finset.mem_sdiff.mp hl).2⟩
  · obtain ⟨l, hl⟩ := exists_starting hx h0
    exact ⟨.suffix l, hl⟩

theorem leftOwners_removed {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p : Pattern T} (hx : x ∈ leftOwners F p) {b : ℕ} (hb : b ≤ T)
    (hxb : x ∈ F b) : p.occurs b := by
  cases p with
  | «prefix» l =>
    simp only [leftOwners, ending, Finset.mem_sdiff] at hx
    change b ≤ l.val
    by_contra hn
    exact hx.2 (hF (by omega) (by omega) hx.1 hxb)
  | «suffix» l =>
    simp only [leftOwners, Finset.mem_sdiff, Finset.mem_inter] at hx
    change l.val < b
    by_contra hn
    exact hx.2 (hF (by omega) (by omega) hxb hx.1.2)

theorem rightOwners_removed {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p : Pattern T} (hx : x ∈ rightOwners F p) {b : ℕ} (hb : b ≤ T)
    (hxb : x ∈ F b) : p.occurs b := by
  cases p with
  | «prefix» l =>
    simp only [rightOwners, Finset.mem_sdiff, Finset.mem_inter] at hx
    change b ≤ l.val
    by_contra hn
    exact hx.2 (hF (by omega) (by omega) hx.1.1 hxb)
  | «suffix» l =>
    simp only [rightOwners, starting, Finset.mem_sdiff] at hx
    change l.val < b
    by_contra hn
    exact hx.2 (hF (by omega) (by omega) hxb hx.1)

theorem leftResidual_avoids {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p : Pattern T} (hx : x ∈ leftResidual F p) {b : ℕ}
    (hb : p.occurs b) : x ∉ F b := by
  cases p with
  | «suffix» l => simpa [leftResidual] using hx
  | «prefix» l =>
    simp only [leftResidual, starting, Finset.mem_sdiff] at hx
    intro hxb
    exact hx.1.2 (hF hb (by omega) hxb hx.1.1)

theorem rightResidual_avoids {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p : Pattern T} (hx : x ∈ rightResidual F p) {b : ℕ}
    (hb : p.occurs b) : x ∉ F b := by
  cases p with
  | «prefix» l => simpa [rightResidual] using hx
  | «suffix» l =>
    simp only [rightResidual, ending, Finset.mem_sdiff] at hx
    intro hxb
    exact hx.1.2 (hF (by omega) (by exact hb) hx.1.1 hxb)

theorem leftResidual_active {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p q : Pattern T} (hx : x ∈ leftResidual F p)
    (hy : x ∈ leftOwners F q) {b : ℕ} (hb : p.occurs b) : q.occurs b := by
  cases p with
  | «suffix» l => simpa [leftResidual] using hx
  | «prefix» l =>
    simp only [leftResidual, starting, Finset.mem_sdiff] at hx
    cases q with
    | «suffix» k => exact (hx.2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2).elim
    | «prefix» k =>
      simp only [leftOwners, ending, Finset.mem_sdiff] at hy
      change b ≤ k.val
      have hle : l.val + 1 ≤ k.val := by
        by_contra hn
        exact hy.2 (hF (by omega) (by omega) hy.1 hx.1.1)
      change b ≤ l.val at hb
      omega

theorem rightResidual_active {F : ℕ → Finset X} (hF : IntervalFamily F)
    {x : X} {p q : Pattern T} (hx : x ∈ rightResidual F p)
    (hy : x ∈ rightOwners F q) {b : ℕ} (hb : p.occurs b) : q.occurs b := by
  cases p with
  | «prefix» l => simpa [rightResidual] using hx
  | «suffix» l =>
    simp only [rightResidual, ending, Finset.mem_sdiff] at hx
    cases q with
    | «prefix» k => exact (hx.2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).1).elim
    | «suffix» k =>
      simp only [rightOwners, starting, Finset.mem_sdiff] at hy
      change k.val < b
      have hle : k.val < l.val := by
        by_contra hn
        exact hy.2 (hF (by omega) (by omega) hx.1.1 hy.1)
      change l.val < b at hb
      omega

theorem leftResidual_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun p q : Pattern T => Disjoint (leftResidual F p) (leftResidual F q)) := by
  intro p q hpq
  cases p with
  | «suffix» l => simp [leftResidual]
  | «prefix» l =>
    cases q with
    | «suffix» k => simp [leftResidual]
    | «prefix» k =>
      exact (starting_disjoint F hF (fun he => hpq (congrArg Pattern.prefix (Fin.ext he)))).mono
        Finset.sdiff_subset Finset.sdiff_subset

theorem rightResidual_disjoint (F : ℕ → Finset X) (hF : IntervalFamily F) :
    Pairwise (fun p q : Pattern T => Disjoint (rightResidual F p) (rightResidual F q)) := by
  intro p q hpq
  cases p with
  | «prefix» l => simp [rightResidual]
  | «suffix» l =>
    cases q with
    | «prefix» k => simp [rightResidual]
    | «suffix» k =>
      exact (ending_disjoint F hF (fun he => hpq (congrArg Pattern.suffix (Fin.ext he)))).mono
        Finset.sdiff_subset Finset.sdiff_subset

theorem left_net_demand (F : ℕ → Finset X) (l : Fin T)
    (hc : (F l.val).card = (F (l.val + 1)).card) :
    (leftOwners F (.prefix l)).card =
      (leftResidual F (.prefix l)).card + (leftOwners F (.suffix l)).card := by
  have he : starting F l.val = leftResidual F (.prefix l) ∪ leftOwners F (.suffix l) := by
    ext x
    simp only [starting, leftResidual, leftOwners, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases h : x ∈ F T <;> simp_all
  have hd : Disjoint (leftResidual F (.prefix l)) (leftOwners F (.suffix l)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).2
  change (F l.val \ F (l.val + 1)).card = _
  rw [Finset.card_sdiff_comm hc]
  change (starting F l.val).card = _
  rw [he, Finset.card_union_of_disjoint hd]

theorem right_net_demand (F : ℕ → Finset X) (l : Fin T)
    (hc : (F l.val).card = (F (l.val + 1)).card) :
    (rightOwners F (.suffix l)).card =
      (rightResidual F (.suffix l)).card + (rightOwners F (.prefix l)).card := by
  have he : ending F l.val = rightResidual F (.suffix l) ∪ rightOwners F (.prefix l) := by
    ext x
    simp only [ending, rightResidual, rightOwners, Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    by_cases h : x ∈ F 0 <;> simp_all
  have hd : Disjoint (rightResidual F (.suffix l)) (rightOwners F (.prefix l)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_inter.mp (Finset.mem_sdiff.mp hy).1).1
  change (F (l.val + 1) \ F l.val).card = _
  rw [Finset.card_sdiff_comm hc.symm]
  change (ending F l.val).card = _
  rw [he, Finset.card_union_of_disjoint hd]

end RigidGHZ.Planar
