module

public import RigidGHZ.Selector.ActiveSupport

@[expose] public section

namespace RigidGHZ.Selector

variable {I W E P : Type*} [Fintype I] [Fintype W] [DecidableEq W]
    [Fintype P] [DecidableEq P] [Nonempty P] [DecidableEq E]
    [AddCommGroup E] [Module ℝ E]

/-- Assign anchors to disjoint finite families of shared nonloop arcs, while
keeping every used loop's prescribed coordinate as its anchor. -/
theorem anchors_from_arc_families
    (p : I → Equiv.Perm W) (tags : W ↪ E) (v : I → E)
    (arcs : P → Finset (W × W))
    (hpair : Pairwise (fun z z' => Disjoint (arcs z) (arcs z')))
    (hnonloop : ∀ z a b, (a, b) ∈ arcs z → a ≠ b)
    (pool : P → Finset E) (hsize : ∀ z, (arcs z).card ≤ (pool z).card)
    (hdisj : ∀ i a b z z', (a, p i a) ∈ arcs z → (b, p i b) ∈ arcs z' → z ≠ z' →
      Disjoint (pool z) (pool z'))
    (hvalid : ∀ i a z, (a, p i a) ∈ arcs z →
      ∀ x ∈ pool z, ∃ t : W, tags t = x + v i)
    (coordinate : W → E)
    (hloopvalid : ∀ i a, p i a = a → ∃ t : W, tags t = coordinate a + v i)
    (hloopinj : ∀ i a b, p i a = a → p i b = b → coordinate a = coordinate b → a = b)
    (hloopsep : ∀ i a b z, p i a = a → (b, p i b) ∈ arcs z → coordinate a ∉ pool z) :
    ∃ givenAnchor : W → W → E,
      (∀ i a, (a = p i a ∨ ∃ z, (a, p i a) ∈ arcs z) →
        ∃ t : W, tags t = givenAnchor a (p i a) + v i) ∧
      ∀ i a b, (a = p i a ∨ ∃ z, (a, p i a) ∈ arcs z) →
        (b = p i b ∨ ∃ z, (b, p i b) ∈ arcs z) →
        givenAnchor a (p i a) = givenAnchor b (p i b) → a = b := by
  classical
  let shared := Finset.univ.biUnion arcs
  let pattern : W × W → P := fun ab =>
    if h : ∃ z, ab ∈ arcs z then h.choose else Classical.choice inferInstance
  have hpattern : ∀ z ab, ab ∈ arcs z → pattern ab = z := by
    intro z ab hab
    have hex : ∃ k, ab ∈ arcs k := ⟨z, hab⟩
    dsimp [pattern]
    rw [dif_pos hex]
    by_contra h
    exact Finset.disjoint_left.mp (hpair h) hex.choose_spec hab
  have hfamily : ∀ ab ∈ shared, ab ∈ arcs (pattern ab) := by
    intro ab hab
    obtain ⟨z, _, hz⟩ := Finset.mem_biUnion.mp hab
    rwa [hpattern z ab hz]
  have hfilter : ∀ z, (shared.filter (fun ab => pattern ab = z)).card ≤ (pool z).card := by
    intro z
    apply (Finset.card_le_card ?_).trans (hsize z)
    intro ab hab
    obtain ⟨ha, hp⟩ := Finset.mem_filter.mp hab
    have hh := hfamily ab ha
    rwa [hp] at hh
  have hused : ∀ i a b, (a, p i a) ∈ shared → (b, p i b) ∈ shared →
      pattern (a, p i a) ≠ pattern (b, p i b) →
      Disjoint (pool (pattern (a, p i a))) (pool (pattern (b, p i b))) := by
    intro i a b ha hb hne
    exact hdisj i a b _ _ (hfamily _ ha) (hfamily _ hb) hne
  obtain ⟨anchor, hmem, hinj⟩ := assign_shared_anchors p shared pattern pool hfilter hused
  let given : W → W → E := fun a b => if a = b then coordinate a else anchor a b
  have hsmem : ∀ a b, (∃ z, (a, b) ∈ arcs z) → (a, b) ∈ shared := by
    rintro a b ⟨z, hz⟩
    exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, hz⟩
  have hshared_of_ne : ∀ i a, (a = p i a ∨ ∃ z, (a, p i a) ∈ arcs z) →
      p i a ≠ a → (a, p i a) ∈ shared := by
    intro i a ha hn
    exact hsmem a _ (ha.resolve_left (Ne.symm hn))
  refine ⟨given, ?_, ?_⟩
  · intro i a ha
    by_cases hf : p i a = a
    · simpa [given, hf] using hloopvalid i a hf
    · have hs := hshared_of_ne i a ha hf
      have hv := hvalid i a _ (hfamily _ hs) _ (hmem a (p i a) hs)
      simpa [given, Ne.symm hf] using hv
  · intro i a b ha hb heq
    by_cases hfa : p i a = a
    · by_cases hfb : p i b = b
      · apply hloopinj i a b hfa hfb
        simpa [given, hfa, hfb] using heq
      · have hs := hshared_of_ne i b hb hfb
        have hm := hmem b (p i b) hs
        have he : coordinate a = anchor b (p i b) := by
          simpa [given, hfa, Ne.symm hfb] using heq
        exact (hloopsep i a b _ hfa (hfamily _ hs) (he.symm ▸ hm)).elim
    · by_cases hfb : p i b = b
      · have hs := hshared_of_ne i a ha hfa
        have hm := hmem a (p i a) hs
        have he : anchor a (p i a) = coordinate b := by
          simpa [given, Ne.symm hfa, hfb] using heq
        exact (hloopsep i b a _ hfb (hfamily _ hs) (he ▸ hm)).elim
      · apply hinj i a b (hshared_of_ne i a ha hfa) (hshared_of_ne i b hb hfb)
        simpa [given, Ne.symm hfa, Ne.symm hfb] using heq

/-- Complete selector assembly from counted shared-arc families and geometric
anchor pools, retaining the ordinary hypergraph's active support. -/
theorem supported_selector_from_arc_families
    (p : I → Equiv.Perm W) (tags : W ↪ E) (v : I → E)
    (arcs : P → Finset (W × W))
    (hpair : Pairwise (fun z z' => Disjoint (arcs z) (arcs z')))
    (hnonloop : ∀ z a b, (a, b) ∈ arcs z → a ≠ b)
    (pool : P → Finset E) (hsize : ∀ z, (arcs z).card ≤ (pool z).card)
    (hdisj : ∀ i a b z z', (a, p i a) ∈ arcs z → (b, p i b) ∈ arcs z' → z ≠ z' →
      Disjoint (pool z) (pool z'))
    (hvalid : ∀ i a z, (a, p i a) ∈ arcs z →
      ∀ x ∈ pool z, ∃ t : W, tags t = x + v i)
    (coordinate : W → E)
    (hloopvalid : ∀ i a, p i a = a → ∃ t : W, tags t = coordinate a + v i)
    (hloopinj : ∀ i a b, p i a = a → p i b = b → coordinate a = coordinate b → a = b)
    (hloopsep : ∀ i a b z, p i a = a → (b, p i b) ∈ arcs z → coordinate a ∉ pool z)
    (hprivate : ∀ i j a, p i a ≠ a → (∀ z, (a, p i a) ∉ arcs z) → p i a = p j a → i = j)
    (L : I → E →ₗ[ℝ] ℝ) (hexposed : ExposedTranslations v L)
    (hcomplete : ∀ q : Equiv.Perm W, (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (U : Finset W) (hfix : ∀ i w, w ∉ U → p i w = w) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧ Nonempty (RigidFamily H I) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x) ∧
      ∀ x : Fin 3 → W, tupleEdge x ∈ H →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  obtain ⟨given, hvalid', hinj'⟩ := anchors_from_arc_families p tags v arcs hpair hnonloop
    pool hsize hdisj hvalid coordinate hloopvalid hloopinj hloopsep
  let Shared : W → W → Prop := fun a b => a = b ∨ ∃ z, (a, b) ∈ arcs z
  have hprivate' : ∀ i j a, ¬ Shared a (p i a) → p i a = p j a → i = j := by
    intro i j a hn heq
    apply hprivate i j a
    · intro h; exact hn (Or.inl h.symm)
    · intro z hz; exact hn (Or.inr ⟨z, hz⟩)
    · exact heq
  obtain ⟨c, anchor, _, htag⟩ := complete_translated_tagging p tags v Shared given
    hvalid' hinj' hprivate'
  exact ⟨selectorHypergraph p c, selectorHypergraph_uniform p c,
    selectorHypergraph_balanced p c,
    ⟨exposed_selector_rigidFamily p c tags anchor v L htag hexposed hcomplete⟩,
    fun _ he => selectorHypergraph_transversal p c he,
    selectorHypergraph_support p c U hfix⟩

end RigidGHZ.Selector
