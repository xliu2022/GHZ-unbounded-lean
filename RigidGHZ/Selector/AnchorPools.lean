module

public import RigidGHZ.Selector.Completion

/-!
# Assigning shared anchors from finite pools

The input is a partition of shared projected arcs into patterns.  Pools may
be reused by patterns that never appear in the same cover.  A cardinal bound
for each pattern and disjointness for simultaneously used patterns suffice
for a globally consistent anchor assignment.
-/

@[expose] public section

namespace RigidGHZ.Selector

variable {I W E P : Type*} [Fintype W] [DecidableEq W] [DecidableEq E]
variable [DecidableEq P] [AddCommGroup E]

theorem assign_shared_anchors
    (p : I → Equiv.Perm W) (shared : Finset (W × W))
    (pattern : W × W → P) (pool : P → Finset E)
    (hsize : ∀ z, (shared.filter (fun ab => pattern ab = z)).card ≤ (pool z).card)
    (hdisj : ∀ i a b, (a, p i a) ∈ shared → (b, p i b) ∈ shared →
      pattern (a, p i a) ≠ pattern (b, p i b) →
      Disjoint (pool (pattern (a, p i a))) (pool (pattern (b, p i b)))) :
    ∃ givenAnchor : W → W → E,
      (∀ a b, (a, b) ∈ shared → givenAnchor a b ∈ pool (pattern (a, b))) ∧
      ∀ i a b, (a, p i a) ∈ shared → (b, p i b) ∈ shared →
        givenAnchor a (p i a) = givenAnchor b (p i b) → a = b := by
  classical
  have hf : ∀ z : P, Nonempty
      (↥(shared.filter (fun ab => pattern ab = z)) ↪ ↥(pool z)) := by
    intro z
    apply Function.Embedding.nonempty_of_card_le
    simpa only [Fintype.card_coe] using hsize z
  let f := fun z => (hf z).some
  let anchor : W → W → E := fun a b =>
    if h : (a, b) ∈ shared then
      (f (pattern (a, b)) ⟨(a, b), Finset.mem_filter.mpr ⟨h, rfl⟩⟩).val
    else 0
  have hf_congr (z z' : P) (hz : z = z') (ab : W × W) (hab : ab ∈ shared)
      (hp : pattern ab = z) (hp' : pattern ab = z') :
      (f z ⟨ab, Finset.mem_filter.mpr ⟨hab, hp⟩⟩).val =
        (f z' ⟨ab, Finset.mem_filter.mpr ⟨hab, hp'⟩⟩).val := by
    subst z'
    rfl
  have hmem : ∀ a b, (a, b) ∈ shared → anchor a b ∈ pool (pattern (a, b)) := by
    intro a b hab
    simp only [anchor, dite_eq_left hab]
    exact (f (pattern (a, b)) ⟨(a, b), Finset.mem_filter.mpr ⟨hab, rfl⟩⟩).property
  refine ⟨anchor, hmem, ?_⟩
  intro i a b ha hb hab
  by_cases hp : pattern (a, p i a) = pattern (b, p i b)
  · have hfa : anchor a (p i a) =
        (f (pattern (b, p i b)) ⟨(a, p i a), Finset.mem_filter.mpr ⟨ha, hp⟩⟩).val := by
      simp only [anchor, dite_eq_left ha]
      exact hf_congr _ _ hp _ ha rfl hp
    have hfb : anchor b (p i b) =
        (f (pattern (b, p i b)) ⟨(b, p i b), Finset.mem_filter.mpr ⟨hb, rfl⟩⟩).val := by
      simp only [anchor, dite_eq_left hb]
    rw [hfa, hfb] at hab
    have he := (f (pattern (b, p i b))).injective (Subtype.ext hab)
    exact congrArg (fun x => x.val.1) he
  · exact False.elim ((Finset.disjoint_left.mp (hdisj i a b ha hb hp))
      (hmem a (p i a) ha) (hab ▸ hmem b (p i b) hb))

variable [Fintype I] [Module ℝ E]

/-- Cardinal estimates and geometric pool conditions suffice to build the
ordinary rigid hypergraph, including all private tags. -/
theorem selector_from_anchor_pools
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
      (∀ a, ∃ i, q a = p i a) → ∃ i, q = p i) :
    ∃ H : Hypergraph (Fin 3 × W), Uniform H 3 ∧
      BalancedPartite H 3 (Fintype.card W) ∧ Nonempty (RigidFamily H I) := by
  obtain ⟨anchor, hmem, hinj⟩ := assign_shared_anchors p shared pattern pool hsize hdisj
  exact complete_exposed_selector p tags v (fun a b => (a, b) ∈ shared) anchor
    (fun i a ha => hvalid i a ha _ (hmem a (p i a) ha)) hinj hprivate L hexposed
    covers_complete

end RigidGHZ.Selector
