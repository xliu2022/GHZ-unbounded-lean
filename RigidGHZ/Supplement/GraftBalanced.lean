module

public import RigidGHZ.Supplement.DegreeRelabel
public import RigidGHZ.RelabelGround

/-! Grafting preserves a balanced multipartition. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Graft

variable {A U W I : Type*} [DecidableEq A] [DecidableEq U] [DecidableEq W]

def oldView : ((A × U) ⊕ A) ≃ (A × Option U) where
  toFun
    | .inl (a, u) => (a, some u)
    | .inr a => (a, none)
  invFun
    | (a, none) => .inr a
    | (a, some u) => .inl (a, u)
  left_inv := by rintro (⟨a, u⟩ | a) <;> rfl
  right_inv := by rintro ⟨a, _ | u⟩ <;> rfl

def newView : ((A × U) ⊕ (A × W)) ≃ (A × (U ⊕ W)) where
  toFun
    | .inl (a, u) => (a, .inl u)
    | .inr (a, w) => (a, .inr w)
  invFun
    | (a, .inl u) => .inl (a, u)
    | (a, .inr w) => .inr (a, w)
  left_inv := by rintro (⟨a, u⟩ | ⟨a, w⟩) <;> rfl
  right_inv := by rintro ⟨a, u | w⟩ <;> rfl

 def graftTuple (x : A → Option U) (z : A → W) (a : A) : U ⊕ W :=
  match x a with
  | none => .inr (z a)
  | some u => .inl u

variable [Fintype A]

 theorem inheritEdge_view (x : A → Option U) (z : A → W) :
    relabelEdge newView (inheritEdge z (relabelEdge oldView.symm (tupleEdge x))) =
      tupleEdge (graftTuple x z) := by
  ext v
  rcases v with ⟨a, u | w⟩
  · rw [mem_relabelEdge]
    change Sum.inl (a, u) ∈ inheritEdge z (relabelEdge oldView.symm (tupleEdge x)) ↔ _
    rw [mem_inherit_left, mem_relabelEdge]
    change (a, some u) ∈ tupleEdge x ↔ (a, Sum.inl u) ∈ tupleEdge (graftTuple x z)
    simp only [mem_tupleEdge]
    cases h : x a <;> simp [graftTuple, h]
  · rw [mem_relabelEdge]
    change Sum.inr (a, w) ∈ inheritEdge z (relabelEdge oldView.symm (tupleEdge x)) ↔ _
    rw [mem_inherit_right, mem_relabelEdge]
    change ((a, none) ∈ tupleEdge x ∧ w = z a) ↔ (a, Sum.inr w) ∈ tupleEdge (graftTuple x z)
    simp only [mem_tupleEdge]
    cases h : x a <;> simp [graftTuple, h]

 theorem internalEdge_view (x : A → W) :
    relabelEdge (newView (U := U)) (internalEdge (tupleEdge x)) = tupleEdge (fun a => Sum.inr (x a)) := by
  ext v
  rcases v with ⟨a, u | w⟩
  · rw [mem_relabelEdge]
    change Sum.inl (a, u) ∈ internalEdge (tupleEdge x) ↔ _
    simp
  · rw [mem_relabelEdge]
    change Sum.inr (a, w) ∈ internalEdge (tupleEdge x) ↔ _
    simp

variable [Fintype U] [Fintype W] [Fintype I]

/-- Grafting in canonical coordinate parts, with all maximum codegree bounds. -/
theorem balanced_family {H : Hypergraph (A × Option U)} {S : Hypergraph (A × W)}
    (L : RigidFamily H I) (R : RigidFamily S I) (a0 : A) (w0 : W)
    (hH : ∀ e ∈ H, ∃ x : A → Option U, e = tupleEdge x)
    (hS : ∀ e ∈ S, ∃ x : A → W, e = tupleEdge x) :
    ∃ G : Hypergraph (A × (U ⊕ W)), Uniform G (Fintype.card A) ∧
      BalancedPartite G (Fintype.card A) (Fintype.card U + Fintype.card W) ∧
      Nonempty (RigidFamily G I) ∧
      ∀ j : ℕ, 1 ≤ j → maxDegree G j ≤ max (maxDegree H j) (maxDegree S j) := by
  classical
  obtain ⟨D⟩ := data_nonempty (L.relabel (oldView (A := A) (U := U)).symm) R a0 w0 hS
  let G := relabelHypergraph (newView (A := A) (U := U) (W := W)) D.graph
  have ht : ∀ e ∈ G, ∃ x : A → U ⊕ W, e = tupleEdge x := by
    intro e he
    obtain ⟨g, hg, rfl⟩ := Finset.mem_image.mp he
    rcases Finset.mem_union.mp hg with hg | hg
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨f0, hf0, rfl⟩ := Finset.mem_image.mp hf
      obtain ⟨x, rfl⟩ := hH f0 hf0
      exact ⟨graftTuple x (D.selector _), inheritEdge_view x (D.selector _)⟩
    · obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨x, rfl⟩ := hS f (Finset.mem_filter.mp hf).1
      exact ⟨fun a => Sum.inr (x a), internalEdge_view x⟩
  refine ⟨G, ?_, ?_, ⟨D.rigidFamily.relabel newView⟩, ?_⟩
  · intro e he
    obtain ⟨x, rfl⟩ := ht e he
    exact tupleEdge_card x
  · simpa only [Fintype.card_sum] using balancedPartite_of_transversal_card G ht
  · intro j hj
    change maxDegree (relabelHypergraph newView D.graph) j ≤ _
    rw [maxDegree_relabel]
    have hd := D.maxDegree_le j hj
    simpa only [maxDegree_relabel] using hd

end RigidGHZ.Supplement.Graft
