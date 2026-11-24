module

public import RigidGHZ.Supplement.Periodic.BitEnumerationFrom

/-! Small compositional equalities for certified finite search outputs. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.BitScheme

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  {D : Scheme V E} (B : BitScheme D)

 theorem enumerateFrom_split (e : E) (es : List E) (A : Finset E) (l o : ℕ)
    (h : l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0) :
    B.enumerateFrom (e :: es) A l o = B.enumerateFrom es A l o ++
      B.enumerateFrom es (insert e A) (B.localMask e ||| l) (B.outMask e ||| o) := by
  rw [enumerateFrom, if_pos h]

 theorem enumerateFrom_split_values (e : E) (es : List E) (A A' : Finset E) (l o l' o' : ℕ)
    (h : l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0)
    (hA : insert e A = A') (hl : B.localMask e ||| l = l') (ho : B.outMask e ||| o = o') :
    B.enumerateFrom (e :: es) A l o = B.enumerateFrom es A l o ++ B.enumerateFrom es A' l' o' := by
  rw [B.enumerateFrom_split e es A l o h, hA, hl, ho]

 theorem enumerateFrom_skip (e : E) (es : List E) (A : Finset E) (l o : ℕ)
    (h : ¬(l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0)) :
    B.enumerateFrom (e :: es) A l o = B.enumerateFrom es A l o := by
  rw [enumerateFrom, if_neg h, List.append_nil]

 theorem enumerate_cons (g : List E) (gs : List (List E)) (A : Finset E) (l o : ℕ) :
    B.enumerate (g :: gs) A l o = g.flatMap (fun e =>
      if l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0 then
        B.enumerate gs (insert e A) (B.localMask e ||| l) (B.outMask e ||| o) else []) := rfl

end RigidGHZ.Supplement.Periodic.BitScheme
