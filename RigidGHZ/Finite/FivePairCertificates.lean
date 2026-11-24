module

public import RigidGHZ.Finite.FivePairData

/-! Small kernel-reduced certificates for the five-point colored bipartite
claim. There are only six orientations at each omitted-point color. All
function assignments are checked; no external classification is assumed. -/

@[expose] public section

namespace RigidGHZ.Finite.FivePair

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

theorem five_row0 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 0 f) →
    extraLeft id (Fin.cons 0 f) = ∅ ∧ extraRight id (Fin.cons 0 f) = ∅ := by
  decide +kernel

theorem five_row1 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 1 f) →
    extraLeft id (Fin.cons 1 f) = ∅ ∧ extraRight id (Fin.cons 1 f) = ∅ := by
  decide +kernel

theorem five_row2 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 2 f) →
    extraLeft id (Fin.cons 2 f) = ∅ ∧ extraRight id (Fin.cons 2 f) = ∅ := by
  decide +kernel

theorem five_row3 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 3 f) →
    extraLeft id (Fin.cons 3 f) = ∅ ∧ extraRight id (Fin.cons 3 f) = ∅ := by
  decide +kernel

theorem five_row4 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 4 f) →
    extraLeft id (Fin.cons 4 f) = ∅ ∧ extraRight id (Fin.cons 4 f) = ∅ := by
  decide +kernel

theorem five_row5 : ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons 5 f) →
    extraLeft id (Fin.cons 5 f) = ∅ ∧ extraRight id (Fin.cons 5 f) = ∅ := by
  decide +kernel

theorem five_rows : ∀ k : Fin 6, ∀ f : Fin 4 → Fin 6,
    CrossFree id (Fin.cons k f) →
    extraLeft id (Fin.cons k f) = ∅ ∧ extraRight id (Fin.cons k f) = ∅ := by
  intro k
  fin_cases k
  · exact five_row0
  · exact five_row1
  · exact five_row2
  · exact five_row3
  · exact five_row4
  · exact five_row5

theorem five_certificate (f : Fin 5 → Fin 6) (h : CrossFree id f) :
    extraLeft id f = ∅ ∧ extraRight id f = ∅ := by
  have hf := five_rows (f 0) (Fin.tail f)
  rw [Fin.cons_self_tail] at hf
  exact hf h

theorem four_row0 : ∀ f : Fin 4 → Fin 6,
    CrossFree (Fin.succAbove (0 : Fin 5)) f →
    (extraLeft (Fin.succAbove (0 : Fin 5)) f).card ≤ 1 ∧
    (extraRight (Fin.succAbove (0 : Fin 5)) f).card ≤ 1 ∧
    ∀ p ∈ extraLeft (Fin.succAbove (0 : Fin 5)) f,
      ∀ q ∈ extraRight (Fin.succAbove (0 : Fin 5)) f, Adj p q := by
  decide +kernel

theorem four_row1 : ∀ f : Fin 4 → Fin 6,
    CrossFree (Fin.succAbove (1 : Fin 5)) f →
    (extraLeft (Fin.succAbove (1 : Fin 5)) f).card ≤ 1 ∧
    (extraRight (Fin.succAbove (1 : Fin 5)) f).card ≤ 1 ∧
    ∀ p ∈ extraLeft (Fin.succAbove (1 : Fin 5)) f,
      ∀ q ∈ extraRight (Fin.succAbove (1 : Fin 5)) f, Adj p q := by
  decide +kernel

theorem four_row2 : ∀ f : Fin 4 → Fin 6,
    CrossFree (Fin.succAbove (2 : Fin 5)) f →
    (extraLeft (Fin.succAbove (2 : Fin 5)) f).card ≤ 1 ∧
    (extraRight (Fin.succAbove (2 : Fin 5)) f).card ≤ 1 ∧
    ∀ p ∈ extraLeft (Fin.succAbove (2 : Fin 5)) f,
      ∀ q ∈ extraRight (Fin.succAbove (2 : Fin 5)) f, Adj p q := by
  decide +kernel

theorem four_row3 : ∀ f : Fin 4 → Fin 6,
    CrossFree (Fin.succAbove (3 : Fin 5)) f →
    (extraLeft (Fin.succAbove (3 : Fin 5)) f).card ≤ 1 ∧
    (extraRight (Fin.succAbove (3 : Fin 5)) f).card ≤ 1 ∧
    ∀ p ∈ extraLeft (Fin.succAbove (3 : Fin 5)) f,
      ∀ q ∈ extraRight (Fin.succAbove (3 : Fin 5)) f, Adj p q := by
  decide +kernel

theorem four_row4 : ∀ f : Fin 4 → Fin 6,
    CrossFree (Fin.succAbove (4 : Fin 5)) f →
    (extraLeft (Fin.succAbove (4 : Fin 5)) f).card ≤ 1 ∧
    (extraRight (Fin.succAbove (4 : Fin 5)) f).card ≤ 1 ∧
    ∀ p ∈ extraLeft (Fin.succAbove (4 : Fin 5)) f,
      ∀ q ∈ extraRight (Fin.succAbove (4 : Fin 5)) f, Adj p q := by
  decide +kernel

theorem four_certificate (c : Fin 5) (f : Fin 4 → Fin 6) (h : CrossFree c.succAbove f) :
    (extraLeft c.succAbove f).card ≤ 1 ∧ (extraRight c.succAbove f).card ≤ 1 ∧
    ∀ p ∈ extraLeft c.succAbove f, ∀ q ∈ extraRight c.succAbove f, Adj p q := by
  fin_cases c
  · exact four_row0 f h
  · exact four_row1 f h
  · exact four_row2 f h
  · exact four_row3 f h
  · exact four_row4 f h

end RigidGHZ.Finite.FivePair
