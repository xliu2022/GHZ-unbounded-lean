module

public import RigidGHZ.Supplement.Periodic.BitEnumeration

/-! The same verified bit representation for unrestricted subset search. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.BitScheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {D : Scheme V E} (B : BitScheme D)

 def enumerateFrom : List E → Finset E → ℕ → ℕ → List (Finset E)
  | [], A, l, _ => if l ||| B.allowed = B.full then [A] else []
  | e :: es, A, l, o => enumerateFrom es A l o ++
      if l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0 then
        enumerateFrom es (insert e A) (B.localMask e ||| l) (B.outMask e ||| o) else []

 theorem enumerateFrom_eq (es : List E) (A : Finset E) (l o : ℕ)
    (hl : decodeBits l = (D.localVertices A).image B.label)
    (ho : decodeBits o = (D.output A).image B.label) :
    B.enumerateFrom es A l o = D.enumerateFrom es A := by
  induction es generalizing A l o with
  | nil => simp only [enumerateFrom, Scheme.enumerateFrom, B.cover_iff hl]
  | cons e es ih =>
    simp only [enumerateFrom, Scheme.enumerateFrom]
    rw [ih A l o hl ho]
    congr 1
    by_cases hc : D.Compatible A e
    · have hm := (B.compatible_iff hl ho e).mpr hc
      simp only [if_pos hm, if_pos hc]
      apply ih
      · rw [decodeBits_or, B.local_correct, hl]
        simp only [Scheme.localVertices, Finset.biUnion_insert, Finset.image_union]
      · rw [decodeBits_or, B.out_correct, ho]
        simp only [Scheme.output, Finset.biUnion_insert, Finset.image_union]
    · have hm : ¬(l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0) :=
        fun h => hc ((B.compatible_iff hl ho e).mp h)
      simp only [if_neg hm, if_neg hc]

end RigidGHZ.Supplement.Periodic.BitScheme
