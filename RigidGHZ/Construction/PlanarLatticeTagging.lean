module

public import RigidGHZ.Construction.PlanarGeometry
public import RigidGHZ.Selector.ArcFamilies
public import RigidGHZ.Selector.Parabola

/-! The exact integral-to-real tagging interface for the one-row planar factor. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Planar

open RigidGHZ.Selector

def realEmbedding : Lattice ↪ (Fin 2 → ℝ) where
  toFun x := ![(x.1 : ℝ), (x.2 : ℝ)]
  inj' := by
    intro x y h
    apply Prod.ext
    · have h0 := congrFun h 0
      simp only [Matrix.cons_val_zero] at h0
      exact_mod_cast h0
    · have h1 := congrFun h 1
      change (x.2 : ℝ) = (y.2 : ℝ) at h1
      exact_mod_cast h1

theorem realEmbedding_translate (b : ℕ) (x : Lattice) :
    realEmbedding (translate b x) = realEmbedding x + planarTranslation (b : ℝ) := by
  funext a
  fin_cases a <;> simp [realEmbedding, translate, planarTranslation, triangular_nat, Rectangle.gamma]

variable {W : Type*} [Fintype W]

def tagEquiv (C : Finset Lattice) (hc : Fintype.card W = C.card) : W ≃ ↥C :=
  Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)

def tagEmbedding (C : Finset Lattice) (hc : Fintype.card W = C.card) : W ↪ (Fin 2 → ℝ) where
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
    (b : ℕ) {x : Lattice} (hx : translate b x ∈ C) :
    ∃ w : W, tagEmbedding C hc w = realEmbedding x + planarTranslation (b : ℝ) := by
  obtain ⟨w, hw⟩ := tagEmbedding_exists C hc hx
  exact ⟨w, hw.trans (realEmbedding_translate b x)⟩

theorem mapped_disjoint {S T : Finset Lattice} (h : Disjoint S T) :
    Disjoint (S.map realEmbedding) (T.map realEmbedding) := by
  apply Finset.disjoint_left.mpr
  intro z hz hz'
  obtain ⟨x, hx, hxe⟩ := Finset.mem_map.mp hz
  obtain ⟨y, hy, hye⟩ := Finset.mem_map.mp hz'
  have hxy := realEmbedding.injective (hxe.trans hye.symm)
  exact Finset.disjoint_left.mp h hx (hxy ▸ hy)

variable [DecidableEq W] {P : Type*} [Fintype P] [DecidableEq P] [Nonempty P]

theorem supported_lattice_selector_from_arc_families (T : ℕ)
    (p : Fin (T + 1) → Equiv.Perm W)
    (C : Finset Lattice) (hc : Fintype.card W = C.card)
    (arcs : P → Finset (W × W))
    (hpair : Pairwise (fun z z' => Disjoint (arcs z) (arcs z')))
    (hnonloop : ∀ z a b, (a, b) ∈ arcs z → a ≠ b)
    (pool : P → Finset Lattice) (hsize : ∀ z, (arcs z).card ≤ (pool z).card)
    (hdisj : ∀ b a a' z z', (a, p b a) ∈ arcs z → (a', p b a') ∈ arcs z' → z ≠ z' →
      Disjoint (pool z) (pool z'))
    (hvalid : ∀ b a z, (a, p b a) ∈ arcs z →
      ∀ x ∈ pool z, translate b.val x ∈ C)
    (coordinate : W → Lattice)
    (hloopvalid : ∀ b a, p b a = a → translate b.val (coordinate a) ∈ C)
    (hloopinj : ∀ b a a', p b a = a → p b a' = a' → coordinate a = coordinate a' → a = a')
    (hloopsep : ∀ b a a' z, p b a = a → (a', p b a') ∈ arcs z → coordinate a ∉ pool z)
    (hprivate : ∀ b c a, p b a ≠ a → (∀ z, (a, p b a) ∉ arcs z) → p b a = p c a → b = c)
    (hcomplete : ∀ q : Equiv.Perm W, (∀ a, ∃ b, q a = p b a) → ∃ b, q = p b)
    (U : Finset W) (hfix : ∀ b w, w ∉ U → p b w = w) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧ Nonempty (RigidFamily H (Fin (T + 1))) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x) ∧
      ∀ x : Fin 3 → W, tupleEdge x ∈ H →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  classical
  refine supported_selector_from_arc_families p (tagEmbedding C hc)
    (fun b => planarTranslation (b.val : ℝ)) arcs hpair hnonloop
    (fun z => (pool z).map realEmbedding) ?_ ?_ ?_
    (fun a => realEmbedding (coordinate a)) ?_ ?_ ?_ hprivate
    (fun b => planarFunctional (b.val : ℝ)) (planar_fin_exposed (T + 1)) hcomplete U hfix
  · simpa only [Finset.card_map] using hsize
  · intro b a a' z z' ha hb hz
    exact mapped_disjoint (hdisj b a a' z z' ha hb hz)
  · intro b a z ha x hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
    exact translated_tag_exists C hc b.val (hvalid b a z ha y hy)
  · intro b a ha
    exact translated_tag_exists C hc b.val (hloopvalid b a ha)
  · intro b a a' ha hb he
    exact hloopinj b a a' ha hb (realEmbedding.injective he)
  · intro b a a' z ha hb hx
    obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hx
    exact hloopsep b a a' z ha hb (realEmbedding.injective he ▸ hy)

end RigidGHZ.Planar
