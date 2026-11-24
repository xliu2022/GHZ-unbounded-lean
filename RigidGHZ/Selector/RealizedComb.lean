module

public import RigidGHZ.Construction.DoubleCombPatterns
public import RigidGHZ.Selector.RealizeBlocks

@[expose] public section

namespace RigidGHZ.Selector

open DoubleComb DoubleComb.Vertex BlockExpansion RigidGHZ.Rectangle

variable {R W : Type*} {T : ℕ} [Fintype R] [DecidableEq R] [Fintype W] [DecidableEq W]

/-- The complete double-comb interface on any finite ground set with specified
owner and private blocks. Its constructor below proves all fields. -/
structure CombRealization (B : Vertex R T → Finset W) where
  perm : (R × Fin (T + 1)) → Equiv.Perm W
  arcs : (R × Pattern T) → Finset (W × W)
  arcs_disjoint : Pairwise (fun p q => Disjoint (arcs p) (arcs q))
  arcs_nonloop : ∀ ip a b, (a, b) ∈ arcs ip → a ≠ b
  arcs_card : ∀ ip, (arcs ip).card = (B (patternVertex ip.1 ip.2)).card
  arcs_occurs : ∀ ib ip a b, (a, b) ∈ arcs ip →
    (perm ib a = b ↔ ip.1 = ib.1 ∧ ip.2.occurs ib.2.val)
  moves_on_block : ∀ ib v w, w ∈ B v → (perm ib w ≠ w ↔ OnRoute ib.1 ib.2 v)
  fix_outside : ∀ ib w, (∀ v, w ∉ B v) → perm ib w = w
  complete : ∀ q : Equiv.Perm W, (∀ a, ∃ ib, q a = perm ib a) → ∃ ib, q = perm ib
  private_unique : ∀ ib jc a, perm ib a ≠ a → (∀ ip, (a, perm ib a) ∉ arcs ip) →
    perm ib a = perm jc a → ib = jc

/-- Order each given block, construct all route permutations, and prove their
exhaustiveness on the original finite ground set. -/
theorem combRealization_nonempty (B : Vertex R T → Finset W)
    (hdisj : Pairwise (fun v w => Disjoint (B v) (B w)))
    (hpos : ∀ v, (B v).Nonempty) (hHub : (B hub).card = 1) : Nonempty (CombRealization B) := by
  classical
  obtain ⟨n, e, hcard, hmem, hiso⟩ := realize_blocks B hdisj hpos
  let Z := {w : W // ∀ v, w ∉ B v}
  let emb : Point n ↪ W := Function.Embedding.inl.trans e.toEmbedding
  let p : R × Fin (T + 1) → Equiv.Perm W := fun ib => e.permCongr (withIsolated n ib)
  let arcs : R × Pattern T → Finset (W × W) := fun ip =>
    (patternArcs n ip.1 ip.2).map (emb.prodMap emb)
  have hnHub : n hub = 0 := by have h := hcard hub; omega
  have hconj : ∀ ib y, p ib (e y) = e (withIsolated n ib y) := by
    intro ib y
    change e (withIsolated n ib (e.symm (e y))) = _
    rw [e.symm_apply_apply]
  have happly : ∀ ib x, p ib (emb x) = emb (expandedPerm n ib.1 ib.2 x) := by
    intro ib x
    exact hconj ib (Sum.inl x)
  have hpre : ∀ v w, w ∈ B v → ∃ k, emb (⟨v, k⟩ : Point n) = w := by
    intro v w hw
    cases he : e.symm w with
    | inl x =>
      rcases x with ⟨u, k⟩
      have hew : e (Sum.inl (⟨u, k⟩ : Point n)) = w := by
        rw [← he]
        exact e.apply_symm_apply w
      have hu : u = v := by
        by_contra huv
        exact Finset.disjoint_left.mp (hdisj huv) (hmem u k) (hew.symm ▸ hw)
      subst u
      exact ⟨k, hew⟩
    | inr z =>
      have hew : z.val = w := by
        have h := e.apply_symm_apply w
        rw [he, hiso z] at h
        exact h
      exact (z.property v (hew.symm ▸ hw)).elim
  have hpoint : ∀ ib w, p ib w ≠ w → ∃ x : Point n, emb x = w := by
    intro ib w hm
    cases he : e.symm w with
    | inl x =>
      refine ⟨x, ?_⟩
      change e (Sum.inl x) = w
      rw [← he]
      exact e.apply_symm_apply w
    | inr z =>
      have hew : e (Sum.inr z) = w := by rw [← he]; exact e.apply_symm_apply w
      apply False.elim
      apply hm
      rw [← hew, hconj]
      rfl
  refine ⟨{
    perm := p
    arcs := arcs
    arcs_disjoint := ?_
    arcs_nonloop := ?_
    arcs_card := ?_
    arcs_occurs := ?_
    moves_on_block := ?_
    fix_outside := ?_
    complete := ?_
    private_unique := ?_
  }⟩
  · intro ip jq hij
    exact (Finset.disjoint_map (emb.prodMap emb)).mpr (patternArcs_pairwise n hij)
  · intro ip a b hab heq
    obtain ⟨⟨x, y⟩, hxy, hmap⟩ := Finset.mem_map.mp hab
    have hx : emb x = a := congrArg Prod.fst hmap
    have hy : emb y = b := congrArg Prod.snd hmap
    exact patternArcs_nonloop n ip.1 ip.2 hxy (emb.injective (hx.trans (heq.trans hy.symm)))
  · intro ip
    change ((patternArcs n ip.1 ip.2).map (emb.prodMap emb)).card = _
    rw [Finset.card_map, patternArcs_card, hcard]
  · intro ib ip a b hab
    obtain ⟨⟨x, y⟩, hxy, hmap⟩ := Finset.mem_map.mp hab
    have hx : emb x = a := congrArg Prod.fst hmap
    have hy : emb y = b := congrArg Prod.snd hmap
    rw [← hx, ← hy, happly]
    exact emb.injective.eq_iff.trans (patternArcs_occurs_iff n ip.1 ib.1 ib.2 ip.2 hxy)
  · intro ib v w hw
    obtain ⟨k, rfl⟩ := hpre v w hw
    rw [happly]
    exact (not_congr emb.injective.eq_iff).trans (expandedPerm_moves_iff n ib.1 ib.2 _)
  · intro ib w hw
    by_contra hm
    obtain ⟨⟨v, k⟩, he⟩ := hpoint ib w hm
    exact hw v (he ▸ hmem v k)
  · exact complete_relabel e (withIsolated n) (withIsolated_complete n)
  · intro ib jc a hm hp heq
    obtain ⟨x, rfl⟩ := hpoint ib a hm
    rw [happly] at hm heq
    rw [happly] at heq
    have hm' : expandedPerm n ib.1 ib.2 x ≠ x := fun h => hm (congrArg emb h)
    apply patternArcs_private_unique n hnHub ib jc x hm'
    · intro ip hxy
      apply hp ip
      rw [happly]
      exact Finset.mem_map.mpr ⟨(x, expandedPerm n ib.1 ib.2 x), hxy, rfl⟩
    · exact emb.injective heq

noncomputable def realizeComb (B : Vertex R T → Finset W)
    (hdisj : Pairwise (fun v w => Disjoint (B v) (B w)))
    (hpos : ∀ v, (B v).Nonempty) (hHub : (B hub).card = 1) : CombRealization B :=
  Classical.choice (combRealization_nonempty B hdisj hpos hHub)

 theorem onRoute_patternVertex (i j : R) (b : Fin (T + 1)) (p : Pattern T) :
    OnRoute i b (patternVertex j p) ↔ j = i ∧ p.occurs b.val := by
  cases p <;> simp [patternVertex, OnRoute, Pattern.occurs, Nat.succ_le_iff]

namespace CombRealization

variable {B : Vertex R T → Finset W} (F : CombRealization B)

/-- The hub and all owner/private blocks are a valid active support. -/
def activeSupport (_F : CombRealization B) : Finset W := Finset.univ.biUnion B

 theorem fixes_complement (ib : R × Fin (T + 1)) (w : W)
    (hw : w ∉ F.activeSupport) : F.perm ib w = w := by
  apply F.fix_outside ib w
  intro v hv
  exact hw (Finset.mem_biUnion.mpr ⟨v, Finset.mem_univ _, hv⟩)

 theorem activeSupport_card (hdisj : Pairwise (fun v w => Disjoint (B v) (B w))) :
    F.activeSupport.card = ∑ v, (B v).card := by
  have hd : ((Finset.univ : Finset (Vertex R T)) : Set (Vertex R T)).PairwiseDisjoint B :=
    fun v hv w hw h => hdisj h
  exact Finset.card_biUnion hd

 theorem moved_pattern (ib : R × Fin (T + 1)) (j : R) (p : Pattern T) {w : W}
    (hw : w ∈ B (patternVertex j p)) :
    F.perm ib w ≠ w ↔ j = ib.1 ∧ p.occurs ib.2.val :=
  (F.moves_on_block ib _ _ hw).trans (onRoute_patternVertex ib.1 j ib.2 p)

end CombRealization
end RigidGHZ.Selector
