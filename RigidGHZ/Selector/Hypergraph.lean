module

public import RigidGHZ.Partite
public import RigidGHZ.Selector.ExposedTranslations
public import Mathlib.Tactic.FinCases

/-!
# The selector as an ordinary hypergraph

This file connects the permutation proof of the exposed-translation selector
to the ordinary finite-set definition of a rigid hypergraph. The three vertex
parts are copies of the same finite type `W`; any third part of equal size may
be transported to `W` along a bijection before applying the theorem.
-/

@[expose] public section

namespace RigidGHZ.Selector

variable {I W E : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable [AddCommGroup E] [Module ℝ E]

/-- Coordinates of each prescribed tripartite perfect matching. -/
def tripartiteCoordinates (p c : I → Equiv.Perm W) : I → Fin 3 → Equiv.Perm W :=
  fun i => ![Equiv.refl W, p i, c i]

/-- The simple hypergraph obtained by lifting each projected arc to its tag. -/
def selectorHypergraph (p c : I → Equiv.Perm W) : Hypergraph (Fin 3 × W) :=
  coordinateHypergraph (fun i a w => tripartiteCoordinates p c i a w)

theorem selectorHypergraph_uniform (p c : I → Equiv.Perm W) :
    Uniform (selectorHypergraph p c) 3 := by
  intro e he
  obtain ⟨i, hi, hei⟩ := Finset.mem_biUnion.mp he
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hei
  simp

theorem selectorHypergraph_balanced (p c : I → Equiv.Perm W) :
    BalancedPartite (selectorHypergraph p c) 3 (Fintype.card W) :=
  coordinateHypergraph_balanced _

/--
Lemma 3.3, after identifying the three equally sized parts with `W`.
The result uses the standard `RigidFamily` predicate: every perfect matching
of the resulting finite simple hypergraph is prescribed, and the prescribed
matchings are pairwise edge-disjoint and partition all its edges.
-/
def exposed_selector_rigidFamily
    (p c : I → Equiv.Perm W)
    (value : W → E) (anchor : W → W → E)
    (v : I → E) (L : I → E →ₗ[ℝ] ℝ)
    (htag : ∀ i a, value (c i a) = anchor a (p i a) + v i)
    (hexposed : ExposedTranslations v L)
    (covers_complete : ∀ q : Equiv.Perm W,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i) :
    RigidFamily (selectorHypergraph p c) I := by
  apply rigidFamily_of_coordinates (0 : Fin 3) (tripartiteCoordinates p c)
  · intro i
    rfl
  · intro i j hij w
    by_cases hp : p i w = p j w
    · refine ⟨2, ?_⟩
      change c i w ≠ c j w
      intro hc
      exact hij (exposed_edge_disjoint p c value anchor v L htag hexposed hp hc)
    · exact ⟨1, hp⟩
  · intro q hq0 hq
    have hsupported : ∀ a, SupportedEdge p c a (q 1 a) (q 2 a) := by
      intro a
      obtain ⟨i, hi⟩ := hq a
      exact ⟨i, hi 1, hi 2⟩
    obtain ⟨i, hq1, hq2⟩ := exposed_selector_complete p c value anchor v L
      htag hexposed covers_complete (q 1) (q 2) hsupported
    refine ⟨i, ?_⟩
    funext a
    fin_cases a
    · exact hq0
    · exact hq1
    · exact hq2

/-- The selector with `d` prescribed covers is `d`-rigid. -/
theorem exposed_selector_isRigid {d : ℕ}
    (p c : Fin d → Equiv.Perm W)
    (value : W → E) (anchor : W → W → E)
    (v : Fin d → E) (L : Fin d → E →ₗ[ℝ] ℝ)
    (htag : ∀ i a, value (c i a) = anchor a (p i a) + v i)
    (hexposed : ExposedTranslations v L)
    (covers_complete : ∀ q : Equiv.Perm W,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i) :
    IsRigid (selectorHypergraph p c) d :=
  ⟨exposed_selector_rigidFamily p c value anchor v L htag hexposed covers_complete⟩

end RigidGHZ.Selector
