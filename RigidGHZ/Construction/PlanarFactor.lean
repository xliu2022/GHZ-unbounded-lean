module

public import RigidGHZ.Construction.PlanarBlockModel
public import RigidGHZ.Construction.PlanarLatticeTagging

/-! Assembly of the planar rigid factor from its concrete owner and anchor geometry. -/

@[expose] public section

namespace RigidGHZ.Planar

open Selector

/-- The geometric planar arrangement gives an actual ordinary rigid hypergraph.
All projection permutations, cycle covers, shared anchors and private tags are constructed. -/
theorem planar_factor_of_arrangement {p h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ p * (T + 1))
    (hh : 4 * Rectangle.gamma T + auxiliaryHeight T ≤ h) (X Z : Finset Lattice)
    (hfull : box 0 (p * (T + 1)) 0 h ⊆ X) (hX : X ⊆ projectionEnvelope (p * (T + 1)) h)
    (hZ : Z ⊆ privatePool p h T) (hZpos : Z.Nonempty)
    (hcard : (tagRegion (p * (T + 1)) h T \ (primaryOne (p * (T + 1)) h T ∪ primaryTwo T ∪ Z)).card = X.card + 1) :
    ∃ H : Hypergraph (Fin 3 × Option ↥X), Uniform H 3 ∧
      BalancedPartite H 3 (X.card + 1) ∧ Nonempty (RigidFamily H (Fin (T + 1))) ∧
      (∀ e ∈ H, ∃ x : Fin 3 → Option ↥X, e = tupleEdge x) ∧
      ∀ x : Fin 3 → Option ↥X, tupleEdge x ∈ H →
        (x 0 ∈ physicalSupport (p * (T + 1)) h T X Z ∧ x 1 ∈ physicalSupport (p * (T + 1)) h T X Z) ∨
        (x 0 = x 1 ∧ x 0 ∉ physicalSupport (p * (T + 1)) h T X Z) := by
  classical
  let W := Option ↥X
  let BS : PlanarComb.Vertex T → Finset W := physicalBlocks (p * (T + 1)) h X Z
  have hd : Pairwise (fun v w => Disjoint (BS v) (BS w)) := physicalBlocks_disjoint hT hw hh X Z hZ
  have hp : ∀ v, (BS v).Nonempty := physicalBlocks_nonempty hT hw hh X Z hfull hZ hZpos
  have hhub : (BS (PlanarComb.hub T)).card = 1 := by simp [BS]
  let F : PlanarComb.Realization BS := PlanarComb.realize BS hd hp hhub
  let C := tagRegion (p * (T + 1)) h T \ (primaryOne (p * (T + 1)) h T ∪ primaryTwo T ∪ Z)
  let pools : Pattern T → Finset Lattice := combinedPool (p * (T + 1)) h
  let coordinate : W → Lattice := fun w => match w with
    | none => (0, 0)
    | some x => x.val
  letI : Nonempty (Pattern T) := ⟨.prefix ⟨0, by omega⟩⟩
  have hC : Fintype.card W = C.card := by
    simp only [W, Fintype.card_option, Fintype.card_coe]
    exact hcard.symm
  have hnone : ∀ b, F.perm b none ≠ none := by
    intro b
    apply (F.moves_on_block b (PlanarComb.hub T) none ?_).mpr
    · exact ⟨rfl, Nat.zero_le _⟩
    · simp [BS]
  have hsize : ∀ q, (F.arcs q).card ≤ (pools q).card := by
    intro q
    rw [F.arcs_card]
    change (physicalBlocks (p * (T + 1)) h X Z (PlanarComb.ownerBlock q)).card ≤ _
    rw [physicalBlocks_pattern, liftLatticeSet_card X _ ((owners_subset_box hw hh q).trans hfull)]
    exact combinedPool_capacity hT hw hh q
  have hdisj : ∀ b a c q r, (a, F.perm b a) ∈ F.arcs q →
      (c, F.perm b c) ∈ F.arcs r → q ≠ r → Disjoint (pools q) (pools r) := by
    intro b a c q r ha hc hqr
    exact combinedPool_disjoint hT hw hh hqr
  have hvalid : ∀ b a q, (a, F.perm b a) ∈ F.arcs q →
      ∀ z ∈ pools q, translate b.val z ∈ C := by
    intro b a q ha z hz
    exact combinedPool_valid hT hw hh Z hZ b q ((F.arcs_occurs b q a _ ha).mp rfl) hz
  have hloopvalid : ∀ b a, F.perm b a = a → translate b.val (coordinate a) ∈ C := by
    intro b a ha
    cases a with
    | none => exact (hnone b ha).elim
    | some x =>
      refine Finset.mem_sdiff.mpr ⟨translate_envelope_mem (by omega) (hX x.property), ?_⟩
      intro hhit
      rcases Finset.mem_union.mp hhit with hprimary | hprivate
      · obtain ⟨q, hq, hqb⟩ := owners_of_hit hw hh (by omega) hprimary
        have hmem : some x ∈ BS (PlanarComb.ownerBlock q) := by
          change some x ∈ physicalBlocks (p * (T + 1)) h X Z (PlanarComb.ownerBlock q)
          rw [physicalBlocks_pattern]
          exact (some_mem_liftLatticeSet X _ x).mpr hq
        exact (F.moved_pattern b q hmem).mpr hqb ha
      · have hmem : some x ∈ BS (PlanarComb.branch b) := by
          change some x ∈ physicalBlocks (p * (T + 1)) h X Z (PlanarComb.branch b)
          rw [physicalBlocks_branch]
          exact (some_mem_liftLatticeSet X _ x).mpr (mem_inverseSet.mpr hprivate)
        exact (F.moves_on_block b _ _ hmem).mpr ⟨rfl, rfl⟩ ha
  have hloopinj : ∀ b a c, F.perm b a = a → F.perm b c = c → coordinate a = coordinate c → a = c := by
    intro b a c ha hc he
    cases a with
    | none => exact (hnone b ha).elim
    | some a =>
      cases c with
      | none => exact (hnone b hc).elim
      | some c => exact congrArg some (Subtype.ext he)
  have hloopsep : ∀ b a c q, F.perm b a = a → (c, F.perm b c) ∈ F.arcs q → coordinate a ∉ pools q := by
    intro b a c q ha hc hx
    have hq := (F.arcs_occurs b q c _ hc).mp rfl
    cases a with
    | none => exact hnone b ha
    | some a =>
      change a.val ∈ externalPool (p * (T + 1)) h q ∪ residual (p * (T + 1)) h q at hx
      rcases Finset.mem_union.mp hx with he | hr
      · exact externalPool_outside hT hw hh q he (hX a.property)
      · obtain ⟨r, hr, hrb⟩ := residual_active hw hh q hr hq
        have hmem : some a ∈ BS (PlanarComb.ownerBlock r) := by
          change some a ∈ physicalBlocks (p * (T + 1)) h X Z (PlanarComb.ownerBlock r)
          rw [physicalBlocks_pattern]
          exact (some_mem_liftLatticeSet X _ a).mpr hr
        exact (F.moved_pattern b r hmem).mpr hrb ha
  have hresult := supported_lattice_selector_from_arc_families T F.perm C hC
    F.arcs F.arcs_disjoint F.arcs_nonloop pools hsize hdisj hvalid
    coordinate hloopvalid hloopinj hloopsep F.private_unique F.complete
    F.activeSupport F.fixes_complement
  simpa only [W, Fintype.card_option, Fintype.card_coe, PlanarComb.Realization.activeSupport,
    BS, physicalSupport] using hresult

end RigidGHZ.Planar
