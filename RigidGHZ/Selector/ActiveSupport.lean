module

public import RigidGHZ.Selector.AnchorPools

@[expose] public section

namespace RigidGHZ.Selector

variable {I W : Type*} [Fintype I] [Fintype W] [DecidableEq W]

theorem selectorHypergraph_transversal (p c : I → Equiv.Perm W)
    {e : Finset (Fin 3 × W)} (he : e ∈ selectorHypergraph p c) :
    ∃ x : Fin 3 → W, e = tupleEdge x := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp he
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hi
  exact ⟨fun a => tripartiteCoordinates p c i a w, hw.symm⟩

theorem selectorHypergraph_support (p c : I → Equiv.Perm W) (U : Finset W)
    (hfix : ∀ i w, w ∉ U → p i w = w)
    (x : Fin 3 → W) (hx : tupleEdge x ∈ selectorHypergraph p c) :
    (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨w, _, hw⟩ := Finset.mem_image.mp hi
  have he : (fun a => tripartiteCoordinates p c i a w) = x := tupleEdge_injective hw
  have h0 : x 0 = w := (congrFun he 0).symm
  have h1 : x 1 = p i w := (congrFun he 1).symm
  rw [h0, h1]
  by_cases hmem : w ∈ U
  · refine Or.inl ⟨hmem, ?_⟩
    by_contra hp
    have h := (p i).injective (hfix i (p i w) hp)
    exact hp (h.symm ▸ hmem)
  · exact Or.inr ⟨(hfix i w hmem).symm, hmem⟩

variable {E P : Type*} [DecidableEq E] [DecidableEq P] [AddCommGroup E] [Module ℝ E]

/-- The anchor-pool construction retains the actual active-support predicate
required by Theorem 3.4. -/
theorem supported_selector_from_anchor_pools
    (p : I → Equiv.Perm W) (tags : W ↪ E) (v : I → E)
    (shared : Finset (W × W)) (pattern : W × W → P) (pool : P → Finset E)
    (hsize : ∀ z, (shared.filter (fun ab => pattern ab = z)).card ≤ (pool z).card)
    (hdisj : ∀ i a b, (a, p i a) ∈ shared → (b, p i b) ∈ shared →
      pattern (a, p i a) ≠ pattern (b, p i b) →
      Disjoint (pool (pattern (a, p i a))) (pool (pattern (b, p i b))))
    (hvalid : ∀ i a, (a, p i a) ∈ shared →
      ∀ x ∈ pool (pattern (a, p i a)), ∃ t : W, tags t = x + v i)
    (hprivate : ∀ i j a, (a, p i a) ∉ shared → p i a = p j a → i = j)
    (L : I → E →ₗ[ℝ] ℝ) (hexposed : ExposedTranslations v L)
    (covers_complete : ∀ q : Equiv.Perm W,
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i)
    (U : Finset W) (hfix : ∀ i w, w ∉ U → p i w = w) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧ Nonempty (RigidFamily H I) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → W, e = tupleEdge x) ∧
      ∀ x : Fin 3 → W, tupleEdge x ∈ H →
        (x 0 ∈ U ∧ x 1 ∈ U) ∨ (x 0 = x 1 ∧ x 0 ∉ U) := by
  obtain ⟨anchor₀, hmem, hinj⟩ := assign_shared_anchors p shared pattern pool hsize hdisj
  obtain ⟨c, anchor, _, htag⟩ := complete_translated_tagging p tags v
    (fun a b => (a, b) ∈ shared) anchor₀
    (fun i a ha => hvalid i a ha _ (hmem a (p i a) ha)) hinj hprivate
  exact ⟨selectorHypergraph p c, selectorHypergraph_uniform p c,
    selectorHypergraph_balanced p c,
    ⟨exposed_selector_rigidFamily p c tags anchor v L htag hexposed covers_complete⟩,
    fun _ he => selectorHypergraph_transversal p c he,
    selectorHypergraph_support p c U hfix⟩

end RigidGHZ.Selector
