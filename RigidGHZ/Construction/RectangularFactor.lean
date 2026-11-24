module

public import RigidGHZ.Construction.CombinedPools
public import RigidGHZ.Construction.LatticeTagging
public import RigidGHZ.Selector.RealizedComb

/-!
# Assembly of the rectangular rigid factor

This theorem takes a geometric arrangement of primary rectangles and private
holes, together with its capacity and cardinality inequalities. It constructs
all projection permutations, all shared anchors, and all private tags, then
proves rigidity for the resulting ordinary tripartite hypergraph.
-/

@[expose] public section

namespace RigidGHZ.Rectangle

open Selector Selector.DoubleComb RectangleAnchors

variable {K : Type*} [Fintype K] [DecidableEq K] {T : ℕ}

def physicalSupport (r : K → PrimaryRectangle) (X Z : Finset Point3) : Finset (Option ↥X) :=
  (Finset.univ : Finset (Vertex (Fin (T + 1)) T)).biUnion (physicalBlocks r X Z)

/-- Abstract rectangular construction. All combinatorial and tagging conclusions
are proved; its inputs are finite geometric placement, capacity, and size facts. -/
theorem rectangular_factor_of_arrangement
    {A B H P : ℕ} (r : K → PrimaryRectangle) (X Z : Finset Point3)
    (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    (hplanes : ∀ k, (r k).plane ≤ P)
    (hZafter : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock r i p ⊆ X)
    (hprivateX : ∀ i b : Fin (T + 1), privateBlock Z i.val b.val ⊆ X)
    (howner : ∀ (i : Fin (T + 1)) (p : Pattern T), (ownerBlock r i p).Nonempty)
    (hZ : Z.Nonempty)
    (hX : X ⊆ projectionEnvelope A B H)
    (hholes : primaryHoles r ∪ Z ⊆ holeBox A B H T)
    (hcapacity : ∀ (i : Fin (T + 1)) (p : Pattern T),
      (ownerBlock r i p).card ≤ externalSupply A B H T p + (residualPool r i p).card)
    (hcard : (tagBox A B H T \ (primaryHoles r ∪ Z)).card = X.card + 1) :
    ∃ G : Hypergraph (Fin 3 × Option ↥X), Uniform G 3 ∧
      BalancedPartite G 3 (X.card + 1) ∧
      Nonempty (RigidFamily G (Fin (T + 1) × Fin (T + 1))) ∧
      (∀ e ∈ G, ∃ x : Fin 3 → Option ↥X, e = tupleEdge x) ∧
      ∀ x : Fin 3 → Option ↥X, tupleEdge x ∈ G →
        (x 0 ∈ physicalSupport (T := T) r X Z ∧ x 1 ∈ physicalSupport (T := T) r X Z) ∨
        (x 0 = x 1 ∧ x 0 ∉ physicalSupport (T := T) r X Z) := by
  classical
  let W := Option ↥X
  let BS : Vertex (Fin (T + 1)) T → Finset W := physicalBlocks r X Z
  have hBSdis : Pairwise (fun v w => Disjoint (BS v) (BS w)) :=
    physicalBlocks_disjoint r X Z hprimary hsep hgrid hplanes hZafter
  have hBSpos : ∀ v, (BS v).Nonempty :=
    physicalBlocks_nonempty r X Z hownerX hprivateX howner hZ
  have hBShub : (BS Vertex.hub).card = 1 := by simp [BS]
  let F : CombRealization BS := realizeComb BS hBSdis hBSpos hBShub
  let C := tagBox A B H T \ (primaryHoles r ∪ Z)
  let pool : Fin (T + 1) × Pattern T → Finset Point3 := fun ip =>
    combinedPool (A := A) (B := B) (H := H) r ip.1 ip.2
  let coordinate : W → Point3 := fun w => match w with
    | none => (0, 0, 0)
    | some x => x.val
  letI : Nonempty (Fin (T + 1) × Pattern T) := ⟨(0, Pattern.full)⟩
  have hC : Fintype.card W = C.card := by
    simp only [W, Fintype.card_option, Fintype.card_coe]
    exact hcard.symm
  have hnone : ∀ ib, F.perm ib none ≠ none := by
    intro ib
    apply (F.moves_on_block ib Vertex.hub none ?_).mpr
    · trivial
    · simp [BS]
  have hsize : ∀ ip, (F.arcs ip).card ≤ (pool ip).card := by
    rintro ⟨i, p⟩
    rw [F.arcs_card]
    change (physicalBlocks r X Z (patternVertex i p)).card ≤ _
    rw [physicalBlocks_pattern, liftLatticeSet_card X _ (hownerX i p)]
    change (ownerBlock r i p).card ≤ (combinedPool (A := A) (B := B) (H := H) r i p).card
    rw [combinedPool_card r X hprimary hsep hownerX hX]
    exact hcapacity i p
  have hdisj : ∀ ib a b ip jq, (a, F.perm ib a) ∈ F.arcs ip →
      (b, F.perm ib b) ∈ F.arcs jq → ip ≠ jq → Disjoint (pool ip) (pool jq) := by
    intro ib a b ip jq ha hb hij
    have hi := (F.arcs_occurs ib ip a _ ha).mp rfl
    have hj := (F.arcs_occurs ib jq b _ hb).mp rfl
    have hpq : ip.2 ≠ jq.2 := by
      intro h
      exact hij (Prod.ext (hi.1.trans hj.1.symm) h)
    have hd := combinedPool_disjoint_when_used r X hprimary hsep hownerX hX
      ib.1 ip.2 jq.2 ib.2.val hpq hi.2 hj.2
    simpa only [pool, hi.1, hj.1] using hd
  have hvalid : ∀ ib a ip, (a, F.perm ib a) ∈ F.arcs ip →
      ∀ z ∈ pool ip, translate ib.1.val ib.2.val z ∈ C := by
    intro ib a ip ha z hz
    have hi := (F.arcs_occurs ib ip a _ ha).mp rfl
    have hz' : z ∈ combinedPool (A := A) (B := B) (H := H) r ib.1 ip.2 := by
      simpa only [pool, hi.1] using hz
    exact combinedPool_valid r X Z hprimary hsep hgrid hplanes hZafter hownerX hX
      hholes ib.1 ib.2 ip.2 hi.2 hz'
  have hloopvalid : ∀ ib a, F.perm ib a = a → translate ib.1.val ib.2.val (coordinate a) ∈ C := by
    intro ib a ha
    cases a with
    | none => exact (hnone ib ha).elim
    | some x =>
      change rowTranslate ib.1.val ib.2.val x.val ∈ C
      apply Finset.mem_sdiff.mpr
      refine ⟨projection_translate_in_tagBox (Nat.le_of_lt_succ ib.1.isLt)
        (Nat.le_of_lt_succ ib.2.isLt) (hX x.property), ?_⟩
      intro hh
      rcases Finset.mem_union.mp hh with hp | hp
      · obtain ⟨pat, hpat, hxpat⟩ := active_owner_of_primary_hit r hprimary hsep ib.1 ib.2 hp
        have hblock : some x ∈ BS (patternVertex ib.1 pat) := by
          change some x ∈ physicalBlocks r X Z (patternVertex ib.1 pat)
          rw [physicalBlocks_pattern]
          exact (some_mem_liftLatticeSet X _ x).mpr hxpat
        exact (F.moved_pattern ib ib.1 pat hblock).mpr ⟨rfl, hpat⟩ ha
      · have hxpriv := (mem_privateBlock_iff Z ib.1.val ib.2.val x.val).mpr hp
        have hblock : some x ∈ BS (Vertex.branch ib.1 ib.2) := by
          change some x ∈ physicalBlocks r X Z (Vertex.branch ib.1 ib.2)
          rw [physicalBlocks_private]
          exact (some_mem_liftLatticeSet X _ x).mpr hxpriv
        exact (F.moves_on_block ib _ _ hblock).mpr ⟨rfl, rfl⟩ ha
  have hloopinj : ∀ ib a b, F.perm ib a = a → F.perm ib b = b → coordinate a = coordinate b → a = b := by
    intro ib a b ha hb he
    cases a with
    | none => exact (hnone ib ha).elim
    | some a =>
      cases b with
      | none => exact (hnone ib hb).elim
      | some b => exact congrArg some (Subtype.ext he)
  have hloopsep : ∀ ib a b ip, F.perm ib a = a → (b, F.perm ib b) ∈ F.arcs ip →
      coordinate a ∉ pool ip := by
    intro ib a b ip ha hb hx
    have hi := (F.arcs_occurs ib ip b _ hb).mp rfl
    cases a with
    | none => exact hnone ib ha
    | some a =>
      change a.val ∈ externalPool A B H T ip.1.val ip.2 ∪ residualPool r ip.1 ip.2 at hx
      rcases Finset.mem_union.mp hx with he | hr
      · exact externalPool_outside ip.1 ip.2 he (hX a.property)
      · have hfull := residualPool_subset_full r hprimary hsep ip.1 ip.2 hr
        have hblock : some a ∈ BS (patternVertex ip.1 Pattern.full) := by
          change some a ∈ physicalBlocks r X Z (patternVertex ip.1 Pattern.full)
          rw [physicalBlocks_pattern]
          exact (some_mem_liftLatticeSet X _ a).mpr hfull
        exact (F.moved_pattern ib ip.1 Pattern.full hblock).mpr ⟨hi.1, trivial⟩ ha
  have hresult := supported_lattice_selector_from_arc_families T F.perm C hC
    F.arcs F.arcs_disjoint F.arcs_nonloop pool hsize hdisj hvalid
    coordinate hloopvalid hloopinj hloopsep F.private_unique F.complete
    F.activeSupport F.fixes_complement
  simpa only [W, Fintype.card_option, Fintype.card_coe, CombRealization.activeSupport,
    BS, physicalSupport] using hresult

end RigidGHZ.Rectangle
