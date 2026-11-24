module

public import RigidGHZ.Supplement.MarkedProjection

/-! Small binary marking codes used by the seed bank. These supply the marking
hypothesis for every seed of at most eight shifts on a base of size at least four. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

 def binaryTriple (n : Fin 8) : Fin 3 → Bool :=
  ![decide (n.val % 2 = 1), decide (n.val / 2 % 2 = 1), decide (n.val / 4 % 2 = 1)]

 theorem binaryTriple_injective : Function.Injective binaryTriple := by decide

variable {m : ℕ} [NeZero m]

 theorem finEquiv_symm_val (a : ZMod m) : ((ZMod.finEquiv m).symm a).val = a.val := by
  cases m with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n => rfl

 def threeMarks (hm : 4 ≤ m) : Finset (Fin m) :=
  {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}

 theorem threeMarks_sum (hm : 4 ≤ m) : ∑ a ∈ threeMarks hm, a.val = 3 := by
  simp [threeMarks, Fin.ext_iff]

 theorem threeMarks_superincreasing (hm : 4 ≤ m) : Marked.Superincreasing (threeMarks hm) := by
  intro a ha hpos
  simp only [threeMarks, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl | rfl <;> norm_num [threeMarks, Fin.lt_def, Finset.filter_insert, Finset.filter_singleton] at *

 def tripleCode {S : Finset (ZMod m)} (e : S ↪ Fin 8) (s : S) (a : ZMod m) : Bool :=
  if h : a.val < 3 then binaryTriple (e s) ⟨a.val, h⟩ else false

 theorem tripleCode_injective {S : Finset (ZMod m)} (hm : 4 ≤ m) (e : S ↪ Fin 8) :
    Function.Injective (tripleCode e) := by
  intro s t he
  apply e.injective
  apply binaryTriple_injective
  funext k
  have hk : k.val < m := lt_of_lt_of_le k.isLt (by omega)
  have hc := congrFun he (k.val : ZMod m)
  simpa only [tripleCode, ZMod.val_natCast_of_lt hk, dite_eq_left k.isLt, Fin.eta] using hc

 theorem tripleCode_outside {S : Finset (ZMod m)} (hm : 4 ≤ m) (e : S ↪ Fin 8)
    (s : S) (a : ZMod m) (ha : (ZMod.finEquiv m).symm a ∉ threeMarks hm) :
    tripleCode e s a = false := by
  have hlarge : ¬ a.val < 3 := by
    intro hsmall
    apply ha
    simp only [threeMarks, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, finEquiv_symm_val]
    omega
  simp [tripleCode, hlarge]

/-- A concrete marking on positions zero, one and two for up to eight shifts. -/
def Marking.binary {S : Finset (ZMod m)} (hm : 4 ≤ m) (hS : S.card ≤ 8) : Marking S := by
  let e : S ↪ Fin 8 := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hS))
  exact {
    marked := threeMarks hm
    sum_lt := by rw [threeMarks_sum]; omega
    superincreasing := threeMarks_superincreasing hm
    code := tripleCode e
    outside := tripleCode_outside hm e
    injective := tripleCode_injective hm e }

 def binaryPair (n : Fin 4) : Fin 2 → Bool :=
  ![decide (n.val % 2 = 1), decide (n.val / 2 % 2 = 1)]

 theorem binaryPair_injective : Function.Injective binaryPair := by decide

 def twoMarks (hm : 2 ≤ m) : Finset (Fin m) :=
  {⟨0, by omega⟩, ⟨1, by omega⟩}

 theorem twoMarks_sum (hm : 2 ≤ m) : ∑ a ∈ twoMarks hm, a.val = 1 := by
  simp [twoMarks, Fin.ext_iff]

 theorem twoMarks_superincreasing (hm : 2 ≤ m) : Marked.Superincreasing (twoMarks hm) := by
  intro a ha hpos
  simp only [twoMarks, Finset.mem_insert, Finset.mem_singleton] at ha
  rcases ha with rfl | rfl <;>
    norm_num [twoMarks, Fin.lt_def, Finset.filter_insert, Finset.filter_singleton] at *

 def pairCode {S : Finset (ZMod m)} (e : S ↪ Fin 4) (s : S) (a : ZMod m) : Bool :=
  if h : a.val < 2 then binaryPair (e s) ⟨a.val, h⟩ else false

 theorem pairCode_injective {S : Finset (ZMod m)} (hm : 2 ≤ m) (e : S ↪ Fin 4) :
    Function.Injective (pairCode e) := by
  intro s t he
  apply e.injective
  apply binaryPair_injective
  funext k
  have hk : k.val < m := lt_of_lt_of_le k.isLt hm
  have hc := congrFun he (k.val : ZMod m)
  simpa only [pairCode, ZMod.val_natCast_of_lt hk, dite_eq_left k.isLt, Fin.eta] using hc

 theorem pairCode_outside {S : Finset (ZMod m)} (hm : 2 ≤ m) (e : S ↪ Fin 4)
    (s : S) (a : ZMod m) (ha : (ZMod.finEquiv m).symm a ∉ twoMarks hm) :
    pairCode e s a = false := by
  have hlarge : ¬ a.val < 2 := by
    intro hsmall
    apply ha
    simp only [twoMarks, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff, finEquiv_symm_val]
    omega
  simp [pairCode, hlarge]

/-- Two marked positions already encode up to four shifts, including the
three-residue seed where the three-position marking is too large. -/
def Marking.binaryTwo {S : Finset (ZMod m)} (hm : 2 ≤ m) (hS : S.card ≤ 4) : Marking S := by
  let e : S ↪ Fin 4 := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hS))
  exact {
    marked := twoMarks hm
    sum_lt := by rw [twoMarks_sum]; omega
    superincreasing := twoMarks_superincreasing hm
    code := pairCode e
    outside := pairCode_outside hm e
    injective := pairCode_injective hm e }

end RigidGHZ.Supplement.Affine
