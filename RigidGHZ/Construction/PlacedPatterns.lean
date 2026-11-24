module

public import RigidGHZ.Construction.PrimaryRectangles

@[expose] public section

namespace RigidGHZ.Rectangle

variable {K : Type*} [Fintype K] [DecidableEq K] {T : ℕ}
    (r : K → PrimaryRectangle)

def ownerBlock (i : Fin (T + 1)) (p : Pattern T) : Finset Point3 :=
  Finset.univ.biUnion (fun k => (p.owners (r k).width (r k).height).map ((r k).ownerEmbedding i.val))

def residualPool (i : Fin (T + 1)) (p : Pattern T) : Finset Point3 :=
  Finset.univ.biUnion (fun k => (p.residual (r k).width (r k).height).map ((r k).ownerEmbedding i.val))

def primaryHoles : Finset Point3 := Finset.univ.biUnion (fun k => (r k).hole)

 theorem owner_map_subset (k : K) (i : Fin (T + 1)) (p : Pattern T) :
    (p.owners (r k).width (r k).height).map ((r k).ownerEmbedding i.val) ⊆ (r k).owners T i.val := by
  rintro x hx
  obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hx
  exact Finset.mem_map.mpr ⟨u, p.owners_subset_union hu, he⟩

 theorem residual_map_subset (k : K) (i : Fin (T + 1)) (p : Pattern T) :
    (p.residual (r k).width (r k).height).map ((r k).ownerEmbedding i.val) ⊆ (r k).owners T i.val := by
  rintro x hx
  obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hx
  exact Finset.mem_map.mpr ⟨u, Pattern.owners_subset_union Pattern.full (p.residual_subset_full hu), he⟩

variable (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))

include hprimary hsep

/-- Every actual primary owner has a unique row and chain pattern even across
all rectangles and all primary levels. -/
theorem ownerBlock_disjoint : Pairwise (fun ip jq : Fin (T + 1) × Pattern T =>
    Disjoint (ownerBlock r ip.1 ip.2) (ownerBlock r jq.1 jq.2)) := by
  rintro ⟨i, p⟩ ⟨j, q⟩ hpq
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hxp
  obtain ⟨l, _, hxl⟩ := Finset.mem_biUnion.mp hxq
  have hok := owner_map_subset r k i p hxk
  have hol := owner_map_subset r l j q hxl
  by_cases hkl : k = l
  · subst l
    have hij : i = j := by
      by_contra h
      exact Finset.disjoint_left.mp ((r k).rows_disjoint (hprimary k) h) hok hol
    subst j
    have hpq' : p ≠ q := by intro h; exact hpq (Prod.ext rfl h)
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hxk
    obtain ⟨v, hv, hf⟩ := Finset.mem_map.mp hxl
    have huv := ((r k).ownerEmbedding i.val).injective (he.trans hf.symm)
    subst v
    exact Finset.disjoint_left.mp (Pattern.owners_disjoint hpq') hu hv
  · exact Finset.disjoint_left.mp
      ((r k).owners_disjoint (r l) (hprimary k) (hprimary l) (hsep hkl) i j) hok hol

 theorem residualPool_subset_full (i : Fin (T + 1)) (p : Pattern T) :
    residualPool r i p ⊆ ownerBlock r i Pattern.full := by
  intro x hx
  obtain ⟨k, hk, hxk⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hxk
  exact Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_map.mpr ⟨u, p.residual_subset_full hu, he⟩⟩

 theorem residualPool_disjoint_when_used (i : Fin (T + 1)) (p q : Pattern T)
    (b : ℕ) (hpq : p ≠ q) (hp : p.occurs b) (hq : q.occurs b) :
    Disjoint (residualPool r i p) (residualPool r i q) := by
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hxp
  obtain ⟨l, _, hxl⟩ := Finset.mem_biUnion.mp hxq
  by_cases hkl : k = l
  · subst l
    obtain ⟨u, hu, he⟩ := Finset.mem_map.mp hxk
    obtain ⟨v, hv, hf⟩ := Finset.mem_map.mp hxl
    have huv := ((r k).ownerEmbedding i.val).injective (he.trans hf.symm)
    subst v
    exact Finset.disjoint_left.mp (p.residual_disjoint_when_used q hpq hp hq) hu hv
  · exact Finset.disjoint_left.mp
      ((r k).owners_disjoint (r l) (hprimary k) (hprimary l) (hsep hkl) i i)
      (residual_map_subset r k i p hxk) (residual_map_subset r l i q hxl)

/-- Residual anchors avoid every primary hole, not just their own rectangle. -/
theorem residualPool_avoids_primary (i b : Fin (T + 1)) (p : Pattern T)
    (hp : p.occurs b.val) {x : Point3} (hx : x ∈ residualPool r i p) :
    rowTranslate i.val b.val x ∉ primaryHoles r := by
  intro hhit
  obtain ⟨k, _, hxk⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨l, _, hl⟩ := Finset.mem_biUnion.mp hhit
  have hok := residual_map_subset r k i p hxk
  have hol : x ∈ (r l).owners T i.val :=
    ((r l).mem_owners_iff T i.val x).mpr ⟨b.val, Nat.le_of_lt_succ b.isLt, hl⟩
  have hkl : k = l := by
    by_contra h
    exact Finset.disjoint_left.mp
      ((r k).owners_disjoint (r l) (hprimary k) (hprimary l) (hsep h) i i) hok hol
  subst l
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hxk
  have hpair := ((r k).mem_hole_translate_iff i.val b.val _).mp hl |>.2
  have hrect := (mem_inverseRectangle_reflect_iff (r k).y
    ((r k).z - (gamma i.val : ℤ)) (r k).width (r k).height b.val u).mp hpair
  exact p.residual_avoids hu hp hrect

/-- Any projection vertex whose translate enters a primary hole lies on an
active owner chain of the selected row and exit. -/
theorem active_owner_of_primary_hit (i b : Fin (T + 1)) {x : Point3}
    (hx : rowTranslate i.val b.val x ∈ primaryHoles r) :
    ∃ p : Pattern T, p.occurs b.val ∧ x ∈ ownerBlock r i p := by
  obtain ⟨k, hk, hhit⟩ := Finset.mem_biUnion.mp hx
  have ho : x ∈ (r k).owners T i.val :=
    ((r k).mem_owners_iff T i.val x).mpr ⟨b.val, Nat.le_of_lt_succ b.isLt, hhit⟩
  obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp ho
  obtain ⟨p, hp, _⟩ := owner_pattern_unique hu
  have hpair := ((r k).mem_hole_translate_iff i.val b.val _).mp hhit |>.2
  have hrect := (mem_inverseRectangle_reflect_iff (r k).y
    ((r k).z - (gamma i.val : ℤ)) (r k).width (r k).height b.val u).mp hpair
  exact ⟨p, p.occurs_of_removed hp (Nat.le_of_lt_succ b.isLt) hrect,
    Finset.mem_biUnion.mpr ⟨k, hk, Finset.mem_map.mpr ⟨u, hp, rfl⟩⟩⟩

 theorem ownerBlock_card (i : Fin (T + 1)) (p : Pattern T) :
    (ownerBlock r i p).card = ∑ k, (p.owners (r k).width (r k).height).card := by
  have hd : ((Finset.univ : Finset K) : Set K).PairwiseDisjoint
      (fun k => (p.owners (r k).width (r k).height).map ((r k).ownerEmbedding i.val)) := by
    intro k hk l hl hkl
    exact ((r k).owners_disjoint (r l) (hprimary k) (hprimary l) (hsep hkl) i i).mono
      (owner_map_subset r k i p) (owner_map_subset r l i p)
  rw [ownerBlock, Finset.card_biUnion hd]
  simp only [Finset.card_map]

 theorem residualPool_card (i : Fin (T + 1)) (p : Pattern T) :
    (residualPool r i p).card = ∑ k, (p.residual (r k).width (r k).height).card := by
  have hd : ((Finset.univ : Finset K) : Set K).PairwiseDisjoint
      (fun k => (p.residual (r k).width (r k).height).map ((r k).ownerEmbedding i.val)) := by
    intro k hk l hl hkl
    exact ((r k).owners_disjoint (r l) (hprimary k) (hprimary l) (hsep hkl) i i).mono
      (residual_map_subset r k i p) (residual_map_subset r l i p)
  rw [residualPool, Finset.card_biUnion hd]
  simp only [Finset.card_map]

 theorem prefixBlock_net_demand (i : Fin (T + 1)) (l : Fin T)
    (hW : ∀ k, T ≤ (r k).width) (hJ : ∀ k, gamma T ≤ (r k).height) :
    (ownerBlock r i (Pattern.prefix l)).card = (residualPool r i (Pattern.prefix l)).card +
      ∑ k, ((r k).height - gamma T + ((r k).width - T + 1) * l.val) := by
  rw [ownerBlock_card r hprimary hsep, residualPool_card r hprimary hsep]
  simp only [Pattern.owners, Pattern.residual]
  simp_rw [prefix_net_demand l.isLt (hW _) (hJ _)]
  exact Finset.sum_add_distrib

 theorem suffixBlock_net_demand (i : Fin (T + 1)) (l : Fin T)
    (hW : ∀ k, T ≤ (r k).width) (hJ : ∀ k, gamma T ≤ (r k).height) :
    (ownerBlock r i (Pattern.suffix l)).card = (residualPool r i (Pattern.suffix l)).card +
      ∑ k, ((r k).height - gamma T + ((r k).width - T + 1) * l.val) := by
  rw [ownerBlock_card r hprimary hsep, residualPool_card r hprimary hsep]
  simp only [Pattern.owners, Pattern.residual]
  simp_rw [suffix_net_demand l.isLt (hW _) (hJ _)]
  exact Finset.sum_add_distrib

 theorem ownerBlock_nonempty (i : Fin (T + 1)) (p : Pattern T)
    (h : ∃ k, (p.owners (r k).width (r k).height).Nonempty) : (ownerBlock r i p).Nonempty := by
  obtain ⟨k, u, hu⟩ := h
  exact ⟨(r k).ownerEmbedding i.val u,
    Finset.mem_biUnion.mpr ⟨k, Finset.mem_univ _, Finset.mem_map.mpr ⟨u, hu, rfl⟩⟩⟩

end RigidGHZ.Rectangle
