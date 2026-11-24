module

public import RigidGHZ.Construction.RectanglePools
public import RigidGHZ.Selector.ActiveSupport
public import RigidGHZ.Selector.ArcFamilies
public import RigidGHZ.Selector.Parabola

/-!
# From integral lattice tags to the exposed-translation selector

This file connects the exact integer geometry to the real linear functionals.
No rounding of a lattice coordinate or a tag value is involved.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.RectangleAnchors

open RigidGHZ.Selector

def realEmbedding : Lattice ↪ (Fin 3 → ℝ) where
  toFun x := ![(x.1 : ℝ), (x.2.1 : ℝ), (x.2.2 : ℝ)]
  inj' := by
    intro x y h
    apply Prod.ext
    · have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero] at h0
      exact_mod_cast h0
    · apply Prod.ext
      · have h1 := congrFun h 1
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at h1
        exact_mod_cast h1
      · have h2 := congrFun h 2
        change (x.2.2 : ℝ) = (y.2.2 : ℝ) at h2
        exact_mod_cast h2

theorem realEmbedding_translate (i b : ℕ) (x : Lattice) :
    realEmbedding (translate i b x) =
      realEmbedding x + rectangularTranslation ((i : ℝ), (b : ℝ)) := by
  funext a
  fin_cases a <;>
    simp [realEmbedding, translate, rectangularTranslation, triangular_nat, Rectangle.gamma, add_assoc]

variable {W : Type*} [Fintype W]

def tagEquiv (C : Finset Lattice) (hc : Fintype.card W = C.card) : W ≃ ↥C :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)

def tagEmbedding (C : Finset Lattice) (hc : Fintype.card W = C.card) : W ↪ (Fin 3 → ℝ) where
  toFun w := realEmbedding (tagEquiv C hc w).val
  inj' := by
    intro x y h
    exact (tagEquiv C hc).injective (Subtype.ext (realEmbedding.injective h))

theorem tagEmbedding_exists (C : Finset Lattice) (hc : Fintype.card W = C.card)
    {x : Lattice} (hx : x ∈ C) : ∃ w : W, tagEmbedding C hc w = realEmbedding x := by
  refine ⟨(tagEquiv C hc).symm ⟨x, hx⟩, ?_⟩
  change realEmbedding ((tagEquiv C hc) ((tagEquiv C hc).symm ⟨x, hx⟩)).val = _
  rw [Equiv.apply_symm_apply]

theorem translated_tag_exists (C : Finset Lattice) (hc : Fintype.card W = C.card)
    (i b : ℕ) {x : Lattice} (hx : translate i b x ∈ C) :
    ∃ w : W, tagEmbedding C hc w =
      realEmbedding x + rectangularTranslation ((i : ℝ), (b : ℝ)) := by
  obtain ⟨w, hw⟩ := tagEmbedding_exists C hc hx
  exact ⟨w, hw.trans (realEmbedding_translate i b x)⟩

theorem mapped_disjoint {S T : Finset Lattice} (h : Disjoint S T) :
    Disjoint (S.map realEmbedding) (T.map realEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hz
  obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp hz'
  have hxy := realEmbedding.injective (hxe.trans hye.symm)
  exact Finset.disjoint_left.mp h hx (hxy ▸ hy)

variable [DecidableEq W] {P : Type*} [DecidableEq P]

/-- An integral pool certificate gives the actual rigid factor, with its active
support, after applying the proved parabolic exposure identities. -/
theorem supported_lattice_selector (T : ℕ)
    (p : (Fin (T + 1) × Fin (T + 1)) → Equiv.Perm W)
    (C : Finset Lattice) (hc : Fintype.card W = C.card)
    (shared : Finset (W × W)) (pattern : W × W → P) (pool : P → Finset Lattice)
    (hsize : ∀ z, (shared.filter (fun ab => pattern ab = z)).card ≤ (pool z).card)
    (hdisj : ∀ i a b, (a, p i a) ∈ shared → (b, p i b) ∈ shared →
      pattern (a, p i a) ≠ pattern (b, p i b) →
      Disjoint (pool (pattern (a, p i a))) (pool (pattern (b, p i b))))
    (hvalid : ∀ i a, (a, p i a) ∈ shared →
      ∀ x ∈ pool (pattern (a, p i a)), translate i.1.val i.2.val x ∈ C)
    (hprivate : ∀ i j a, (a, p i a) ∉ shared → p i a = p j a → i = j)
    (covers_complete : ∀ q : Equiv.Perm W,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (U : Finset W) (hfix : ∀ i w, w ∉ U → p i w = w) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧
      Nonempty (RigidFamily H (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x) ∧
      ∀ x : Fin 3 → W, tupleEdge x ∈ H →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  classical
  refine supported_selector_from_anchor_pools p (tagEmbedding C hc)
    (fun i => rectangularTranslation ((i.1.val : ℝ), (i.2.val : ℝ)))
    shared pattern (fun z => (pool z).map realEmbedding)
    ?_ ?_ ?_ hprivate
    (fun i => rectangularFunctional ((i.1.val : ℝ), (i.2.val : ℝ)))
    (rectangular_fin_exposed (T + 1)) covers_complete U hfix
  · simpa only [Finset.card_map] using hsize
  · intro i a b ha hb hp
    exact mapped_disjoint (hdisj i a b ha hb hp)
  · intro i a ha z hz
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hz
    exact translated_tag_exists C hc i.1.val i.2.val (hvalid i a ha x hx)

/-- Version with named families of nonloop arcs. Loops retain the integral
coordinate of their vertices, so their validity and separation remain explicit. -/
theorem supported_lattice_selector_from_arc_families [Fintype P] [Nonempty P] (T : ℕ)
    (p : (Fin (T + 1) × Fin (T + 1)) → Equiv.Perm W)
    (C : Finset Lattice) (hc : Fintype.card W = C.card)
    (arcs : P → Finset (W × W))
    (hpair : Pairwise (fun z z' => Disjoint (arcs z) (arcs z')))
    (hnonloop : ∀ z a b, (a, b) ∈ arcs z → a ≠ b)
    (pool : P → Finset Lattice) (hsize : ∀ z, (arcs z).card ≤ (pool z).card)
    (hdisj : ∀ i a b z z', (a, p i a) ∈ arcs z → (b, p i b) ∈ arcs z' → z ≠ z' →
      Disjoint (pool z) (pool z'))
    (hvalid : ∀ i a z, (a, p i a) ∈ arcs z →
      ∀ x ∈ pool z, translate i.1.val i.2.val x ∈ C)
    (coordinate : W → Lattice)
    (hloopvalid : ∀ i a, p i a = a → translate i.1.val i.2.val (coordinate a) ∈ C)
    (hloopinj : ∀ i a b, p i a = a → p i b = b → coordinate a = coordinate b → a = b)
    (hloopsep : ∀ i a b z, p i a = a → (b, p i b) ∈ arcs z → coordinate a ∉ pool z)
    (hprivate : ∀ i j a, p i a ≠ a → (∀ z, (a, p i a) ∉ arcs z) →
      p i a = p j a → i = j)
    (hcomplete : ∀ q : Equiv.Perm W, (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (U : Finset W) (hfix : ∀ i w, w ∉ U → p i w = w) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧
      Nonempty (RigidFamily H (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x) ∧
      ∀ x : Fin 3 → W, tupleEdge x ∈ H →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  classical
  refine supported_selector_from_arc_families p (tagEmbedding C hc)
    (fun i => rectangularTranslation ((i.1.val : ℝ), (i.2.val : ℝ)))
    arcs hpair hnonloop (fun z => (pool z).map realEmbedding)
    ?_ ?_ ?_ (fun a => realEmbedding (coordinate a)) ?_ ?_ ?_ hprivate
    (fun i => rectangularFunctional ((i.1.val : ℝ), (i.2.val : ℝ)))
    (rectangular_fin_exposed (T + 1)) hcomplete U hfix
  · simpa only [Finset.card_map] using hsize
  · intro i a b z z' ha hb hz
    exact mapped_disjoint (hdisj i a b z z' ha hb hz)
  · intro i a z ha x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact translated_tag_exists C hc i.1.val i.2.val (hvalid i a z ha y hy)
  · intro i a ha
    exact translated_tag_exists C hc i.1.val i.2.val (hloopvalid i a ha)
  · intro i a b ha hb he
    exact hloopinj i a b ha hb (realEmbedding.injective he)
  · intro i a b z ha hb hx
    obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hx
    exact hloopsep i a b z ha hb (realEmbedding.injective he ▸ hy)

end RigidGHZ.RectangleAnchors
