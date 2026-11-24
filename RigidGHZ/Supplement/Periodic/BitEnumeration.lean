module

public import RigidGHZ.Supplement.Periodic.GroupedEnumeration
public import Mathlib.Data.Nat.BitIndices
public import Mathlib.Data.Nat.Bitwise

/-! A verified bit-mask implementation of the exact local-configuration search.
This changes only representation and evaluation cost, never the search space. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic

 def decodeBits (n : ℕ) : Finset ℕ := n.bitIndices.toFinset

@[simp] theorem mem_decodeBits (i n : ℕ) : i ∈ decodeBits n ↔ n.testBit i := by
  simp [decodeBits]

@[simp] theorem decodeBits_zero : decodeBits 0 = ∅ := by simp [decodeBits]

 theorem decodeBits_injective : Function.Injective decodeBits := by
  intro a b hab
  apply Nat.eq_of_testBit_eq
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [← mem_decodeBits, ← mem_decodeBits, hab]

 theorem decodeBits_or (a b : ℕ) : decodeBits (a ||| b) = decodeBits a ∪ decodeBits b := by
  ext i
  simp [Nat.testBit_lor]

 theorem decodeBits_and (a b : ℕ) : decodeBits (a &&& b) = decodeBits a ∩ decodeBits b := by
  ext i
  simp [Nat.testBit_land]

 theorem land_zero_iff (a b : ℕ) : a &&& b = 0 ↔ Disjoint (decodeBits a) (decodeBits b) := by
  rw [← decodeBits_injective.eq_iff, decodeBits_and, decodeBits_zero, Finset.disjoint_iff_inter_eq_empty]

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

 structure BitScheme (D : Scheme V E) where
  label : V ↪ ℕ
  localMask : E → ℕ
  outMask : E → ℕ
  full : ℕ
  allowed : ℕ
  local_correct : ∀ e, decodeBits (localMask e) = (D.localPart e).image label
  out_correct : ∀ e, decodeBits (outMask e) = (D.outgoing e).image label
  full_correct : decodeBits full = Finset.univ.image label
  allowed_correct : decodeBits allowed = D.allOutgoing.image label

namespace BitScheme

variable {D : Scheme V E} (B : BitScheme D)

 def enumerate : List (List E) → Finset E → ℕ → ℕ → List (Finset E)
  | [], A, l, _ => if l ||| B.allowed = B.full then [A] else []
  | g :: gs, A, l, o => g.flatMap (fun e =>
      if l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0 then
        enumerate gs (insert e A) (B.localMask e ||| l) (B.outMask e ||| o) else [])

 theorem compatible_iff {A : Finset E} {l o : ℕ}
    (hl : decodeBits l = (D.localVertices A).image B.label)
    (ho : decodeBits o = (D.output A).image B.label) (e : E) :
    (l &&& B.localMask e = 0 ∧ o &&& B.outMask e = 0) ↔ D.Compatible A e := by
  rw [land_zero_iff, land_zero_iff, hl, ho, B.local_correct, B.out_correct,
    Finset.disjoint_image B.label.injective, Finset.disjoint_image B.label.injective]
  rfl

 theorem cover_iff {A : Finset E} {l : ℕ}
    (hl : decodeBits l = (D.localVertices A).image B.label) :
    l ||| B.allowed = B.full ↔ D.input A ⊆ D.allOutgoing := by
  have hu : D.input A ⊆ D.allOutgoing ↔ D.localVertices A ∪ D.allOutgoing = Finset.univ := by
    constructor
    · intro h
      ext v
      simp only [Finset.mem_union, Finset.mem_univ, iff_true]
      by_cases hv : v ∈ D.localVertices A
      · exact Or.inl hv
      · exact Or.inr (h (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hv⟩))
    · intro h v hv
      have hm : v ∈ D.localVertices A ∪ D.allOutgoing := by rw [h]; exact Finset.mem_univ _
      exact (Finset.mem_union.mp hm).resolve_left (Finset.mem_sdiff.mp hv).2
  rw [hu, ← decodeBits_injective.eq_iff, decodeBits_or, hl, B.allowed_correct, B.full_correct,
    ← Finset.image_union, Finset.image_inj B.label.injective]

/-- Exact extensional equality with the finite-set enumerator already proved
complete for all ordinary local configurations. -/
theorem enumerate_eq (gs : List (List E)) (A : Finset E) (l o : ℕ)
    (hl : decodeBits l = (D.localVertices A).image B.label)
    (ho : decodeBits o = (D.output A).image B.label) :
    B.enumerate gs A l o = D.enumerateGroups gs A := by
  induction gs generalizing A l o with
  | nil => simp only [enumerate, Scheme.enumerateGroups, B.cover_iff hl]
  | cons g gs ih =>
    simp only [enumerate, Scheme.enumerateGroups]
    congr 1
    funext e
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

end BitScheme
end RigidGHZ.Supplement.Periodic
