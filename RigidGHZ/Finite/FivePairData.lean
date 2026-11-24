module

public import RigidGHZ.Basic
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fin.SuccPred

/-! The bipartite graph in Appendix B, Claim B.1. Each side consists of the
actual two-element subsets of a five-element set. -/

@[expose] public section

namespace RigidGHZ.Finite.FivePair

abbrev Pair := {p : Finset (Fin 5) // p.card = 2}

def Adj (p q : Pair) : Prop := Disjoint p.val q.val

instance adjDecidable (p q : Pair) : Decidable (Adj p q) := by
  unfold Adj
  infer_instance

/-- On an adjacent pair this is exactly the point outside their union. The
total of the integer representatives of the five points is ten. -/
def color (p q : Pair) : Fin 5 :=
  ⟨(10 - (∑ x ∈ p.val, x.val) - (∑ x ∈ q.val, x.val)) % 5, Nat.mod_lt _ (by decide)⟩

theorem color_correct (p q : Pair) (h : Adj p q) :
    p.val ∪ q.val = Finset.univ.erase (color p q) := by
  have hc : ∀ p q : Pair, Adj p q →
      p.val ∪ q.val = Finset.univ.erase (color p q) := by decide +kernel
  exact hc p q h

def choiceSet : Fin 5 → Fin 6 → Finset (Fin 5) := ![
  ![{1,2}, {1,3}, {1,4}, {2,3}, {2,4}, {3,4}],
  ![{0,2}, {0,3}, {0,4}, {2,3}, {2,4}, {3,4}],
  ![{0,1}, {0,3}, {0,4}, {1,3}, {1,4}, {3,4}],
  ![{0,1}, {0,2}, {0,4}, {1,2}, {1,4}, {2,4}],
  ![{0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}]]

theorem choiceSet_card (c : Fin 5) (j : Fin 6) : (choiceSet c j).card = 2 := by
  have h : ∀ c j, (choiceSet c j).card = 2 := by decide +kernel
  exact h c j

def choice (c : Fin 5) (j : Fin 6) : Pair := ⟨choiceSet c j, choiceSet_card c j⟩

def partner (c : Fin 5) (j : Fin 6) : Pair := choice c j.rev

theorem choice_adj (c : Fin 5) (j : Fin 6) : Adj (choice c j) (partner c j) := by
  have h : ∀ c j, Adj (choice c j) (partner c j) := by decide +kernel
  exact h c j

theorem choice_color (c : Fin 5) (j : Fin 6) : color (choice c j) (partner c j) = c := by
  have h : ∀ c j, color (choice c j) (partner c j) = c := by decide +kernel
  exact h c j

theorem choice_complete (c : Fin 5) (p q : Pair) (ha : Adj p q)
    (hc : color p q = c) : ∃ j : Fin 6, p = choice c j ∧ q = partner c j := by
  have h : ∀ c : Fin 5, ∀ p q : Pair, Adj p q → color p q = c →
      ∃ j : Fin 6, p = choice c j ∧ q = partner c j := by decide +kernel
  exact h c p q ha hc

def edges (L R : Finset Pair) : Finset (Pair × Pair) :=
  (L.product R).filter (fun e => Adj e.1 e.2)

theorem mem_edges {L R : Finset Pair} {p q : Pair} :
    (p, q) ∈ edges L R ↔ p ∈ L ∧ q ∈ R ∧ Adj p q := by
  constructor
  · intro h
    obtain ⟨hpq, ha⟩ := Finset.mem_filter.mp h
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    exact ⟨hp, hq, ha⟩
  · rintro ⟨hp, hq, ha⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, hq⟩, ha⟩

/-- Maximum induced degree at most one, and pairwise distinct omitted-point
colors on the induced edges. These are exactly the hypotheses of Claim B.1. -/
structure Conditions (L R : Finset Pair) : Prop where
  left_unique : ∀ p ∈ L, ∀ q ∈ R, ∀ q' ∈ R, Adj p q → Adj p q' → q = q'
  right_unique : ∀ q ∈ R, ∀ p ∈ L, ∀ p' ∈ L, Adj p q → Adj p' q → p = p'
  color_unique : ∀ e ∈ edges L R, ∀ f ∈ edges L R,
    color e.1 e.2 = color f.1 f.2 → e = f

variable {I : Type*} [Fintype I] [DecidableEq I]

def CrossFree (c : I → Fin 5) (f : I → Fin 6) : Prop :=
  ∀ i j, i ≠ j → ¬Adj (choice (c i) (f i)) (partner (c j) (f j))

instance crossFreeDecidable (c : I → Fin 5) (f : I → Fin 6) : Decidable (CrossFree c f) := by
  unfold CrossFree
  infer_instance

def extraLeft (c : I → Fin 5) (f : I → Fin 6) : Finset Pair :=
  Finset.univ.filter (fun p => ∀ i, ¬Adj p (partner (c i) (f i)))

def extraRight (c : I → Fin 5) (f : I → Fin 6) : Finset Pair :=
  Finset.univ.filter (fun q => ∀ i, ¬Adj (choice (c i) (f i)) q)

def leftFamily (c : I → Fin 5) (f : I → Fin 6) : Finset Pair :=
  Finset.univ.image (fun i => choice (c i) (f i))

def rightFamily (c : I → Fin 5) (f : I → Fin 6) : Finset Pair :=
  Finset.univ.image (fun i => partner (c i) (f i))

def edgeFamily (c : I → Fin 5) (f : I → Fin 6) : Finset (Pair × Pair) :=
  Finset.univ.image (fun i => (choice (c i) (f i), partner (c i) (f i)))

end RigidGHZ.Finite.FivePair
