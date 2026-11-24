module

public import RigidGHZ.Construction.PlanarPools

/-! Combined planar owner blocks, residual pools, and their exact net demands. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

def firstFamily (w h T : ℕ) := inverseSet (primaryOne w h T)
def secondFamily (T : ℕ) := inverseSet (primaryTwo T)

def owners (w h : ℕ) {T : ℕ} (p : Pattern T) : Finset Lattice :=
  leftOwners (firstFamily w h T) p ∪ rightOwners (secondFamily T) p

def residual (w h : ℕ) {T : ℕ} (p : Pattern T) : Finset Lattice :=
  leftResidual (firstFamily w h T) p ∪ rightResidual (secondFamily T) p

def combinedPool (w h : ℕ) {T : ℕ} (p : Pattern T) : Finset Lattice :=
  externalPool w h p ∪ residual w h p

theorem firstFamily_interval {w h T : ℕ} (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    IntervalFamily (firstFamily w h T) := by
  intro a b c hab hbc x ha hc
  exact mem_inverseSet.mpr (primaryOne_between hab hbc hw hh (mem_inverseSet.mp ha) (mem_inverseSet.mp hc))

theorem secondFamily_interval (T : ℕ) : IntervalFamily (secondFamily T) := by
  intro a b c hab hbc x ha hc
  exact mem_inverseSet.mpr (primaryTwo_between hab hbc (mem_inverseSet.mp ha) (mem_inverseSet.mp hc))

theorem firstFamily_proper (w h T : ℕ) : Disjoint (firstFamily w h T 0) (firstFamily w h T T) := by
  apply Finset.disjoint_left.mpr
  intro x h0 hT
  exact primaryOne_proper w h T (mem_inverseSet.mp h0) (mem_inverseSet.mp hT)

theorem secondFamily_proper (T : ℕ) : Disjoint (secondFamily T 0) (secondFamily T T) := by
  apply Finset.disjoint_left.mpr
  intro x h0 hT
  exact primaryTwo_proper T (mem_inverseSet.mp h0) (mem_inverseSet.mp hT)

theorem leftOwners_hit {F : ℕ → Finset Lattice} {T : ℕ} (p : Pattern T) {x : Lattice}
    (hx : x ∈ leftOwners F p) : ∃ b ≤ T, x ∈ F b := by
  cases p with
  | «prefix» l => exact ⟨l.val, by omega, (Finset.mem_sdiff.mp hx).1⟩
  | «suffix» l => exact ⟨l.val + 1, by omega, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).1⟩

theorem rightOwners_hit {F : ℕ → Finset Lattice} {T : ℕ} (p : Pattern T) {x : Lattice}
    (hx : x ∈ rightOwners F p) : ∃ b ≤ T, x ∈ F b := by
  cases p with
  | «prefix» l => exact ⟨l.val, by omega, (Finset.mem_inter.mp (Finset.mem_sdiff.mp hx).1).2⟩
  | «suffix» l => exact ⟨l.val + 1, by omega, (Finset.mem_sdiff.mp hx).1⟩

theorem leftResidual_hit {F : ℕ → Finset Lattice} {T : ℕ} (p : Pattern T) {x : Lattice}
    (hx : x ∈ leftResidual F p) : ∃ b ≤ T, x ∈ F b := by
  cases p with
  | «prefix» l => exact ⟨l.val + 1, by omega, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1⟩
  | «suffix» l => simpa [leftResidual] using hx

theorem rightResidual_hit {F : ℕ → Finset Lattice} {T : ℕ} (p : Pattern T) {x : Lattice}
    (hx : x ∈ rightResidual F p) : ∃ b ≤ T, x ∈ F b := by
  cases p with
  | «prefix» l => simpa [rightResidual] using hx
  | «suffix» l => exact ⟨l.val, by omega, (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp hx).1).1⟩

theorem primary_families_separate {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) {x : Lattice}
    (h1 : ∃ b ≤ T, x ∈ firstFamily w h T b) (h2 : ∃ c ≤ T, x ∈ secondFamily T c) : False := by
  obtain ⟨b, hb, h1⟩ := h1
  obtain ⟨c, hc, h2⟩ := h2
  exact Finset.disjoint_left.mp (primary_owner_disjoint hb hc hw (by omega)) h1 h2

theorem owners_disjoint {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) :
    Pairwise (fun p q : Pattern T => Disjoint (owners w h p) (owners w h q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact Finset.disjoint_left.mp (leftOwners_disjoint _ (firstFamily_interval (by omega) (by omega)) hpq) hx hy
  · exact primary_families_separate hw hh (leftOwners_hit p hx) (rightOwners_hit q hy)
  · exact primary_families_separate hw hh (leftOwners_hit q hy) (rightOwners_hit p hx)
  · exact Finset.disjoint_left.mp (rightOwners_disjoint _ (secondFamily_interval T) hpq) hx hy

theorem residual_disjoint {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) :
    Pairwise (fun p q : Pattern T => Disjoint (residual w h p) (residual w h q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact Finset.disjoint_left.mp (leftResidual_disjoint _ (firstFamily_interval (by omega) (by omega)) hpq) hx hy
  · exact primary_families_separate hw hh (leftResidual_hit p hx) (rightResidual_hit q hy)
  · exact primary_families_separate hw hh (leftResidual_hit q hy) (rightResidual_hit p hx)
  · exact Finset.disjoint_left.mp (rightResidual_disjoint _ (secondFamily_interval T) hpq) hx hy

theorem owners_subset_box {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    owners w h p ⊆ box 0 w 0 h := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨b, hb, hx⟩ := leftOwners_hit p hx
    exact (primaryOne_inverse_envelope hb (by omega) (by omega) (mem_inverseSet.mp hx)).1
  · obtain ⟨b, hb, hx⟩ := rightOwners_hit p hx
    exact (primaryTwo_inverse_envelope hb hw (by omega) (mem_inverseSet.mp hx)).1

theorem residual_subset_box {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    residual w h p ⊆ box 0 w 0 h := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨b, hb, hx⟩ := leftResidual_hit p hx
    exact (primaryOne_inverse_envelope hb (by omega) (by omega) (mem_inverseSet.mp hx)).1
  · obtain ⟨b, hb, hx⟩ := rightResidual_hit p hx
    exact (primaryTwo_inverse_envelope hb hw (by omega) (mem_inverseSet.mp hx)).1

theorem fullBox_subset_envelope (w h : ℕ) : box 0 w 0 h ⊆ projectionEnvelope w h := by
  intro x hx
  simp only [box, projectionEnvelope, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

theorem owners_of_hit {w h T b : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (hb : b ≤ T)
    {x : Lattice} (hx : translate b x ∈ primaryOne w h T ∪ primaryTwo T) :
    ∃ p : Pattern T, x ∈ owners w h p ∧ p.occurs b := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have hhit : x ∈ firstFamily w h T b := mem_inverseSet.mpr hx
    obtain ⟨p, hp⟩ := leftOwners_cover (firstFamily_proper w h T) ⟨b, hb, hhit⟩
    exact ⟨p, Finset.mem_union_left _ hp,
      leftOwners_removed (firstFamily_interval (by omega) (by omega)) hp hb hhit⟩
  · have hhit : x ∈ secondFamily T b := mem_inverseSet.mpr hx
    obtain ⟨p, hp⟩ := rightOwners_cover (secondFamily_proper T) ⟨b, hb, hhit⟩
    exact ⟨p, Finset.mem_union_right _ hp, rightOwners_removed (secondFamily_interval T) hp hb hhit⟩

theorem residual_active {w h T b : ℕ} (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T)
    {x : Lattice} (hx : x ∈ residual w h p) (hp : p.occurs b) :
    ∃ q : Pattern T, x ∈ owners w h q ∧ q.occurs b := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨q, hq⟩ := leftOwners_cover (firstFamily_proper w h T) (leftResidual_hit p hx)
    exact ⟨q, Finset.mem_union_left _ hq,
      leftResidual_active (firstFamily_interval (by omega) (by omega)) hx hq hp⟩
  · obtain ⟨q, hq⟩ := rightOwners_cover (secondFamily_proper T) (rightResidual_hit p hx)
    exact ⟨q, Finset.mem_union_right _ hq, rightResidual_active (secondFamily_interval T) hx hq hp⟩

theorem owner_residual_net {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    ((owners w h p).card : ℤ) = (residual w h p).card +
      match p with
      | .prefix l => externalDemand w h T (l.val + 1)
      | .suffix l => externalDemand w h T (l.val + 1) := by
  have hd : ∀ p : Pattern T, Disjoint (leftOwners (firstFamily w h T) p) (rightOwners (secondFamily T) p) := by
    intro p
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact primary_families_separate hw hh (leftOwners_hit p hx) (rightOwners_hit p hy)
  have hc1 : ∀ l : Fin T, ((firstFamily w h T) l.val).card = ((firstFamily w h T) (l.val + 1)).card := by
    intro l; simp [firstFamily]
  have hc2 : ∀ l : Fin T, ((secondFamily T) l.val).card = ((secondFamily T) (l.val + 1)).card := by
    intro l; simp [secondFamily]
  have hs : ∀ l : Fin T, leftOwners (firstFamily w h T) (.suffix l) = firstSuffixOwners w h T (l.val + 1) := by
    intro l; simp [leftOwners, firstFamily, firstSuffixOwners]
  have hp : ∀ l : Fin T, rightOwners (secondFamily T) (.prefix l) = secondPrefixOwners T (l.val + 1) := by
    intro l; simp [rightOwners, secondFamily, secondPrefixOwners]
  rw [owners, Finset.card_union_of_disjoint (hd p), Nat.cast_add]
  cases p with
  | «prefix» l =>
    have he := left_net_demand (firstFamily w h T) l (hc1 l)
    rw [he, Nat.cast_add, hs l, hp l]
    have hn := net_external_demand hT (by omega) (by omega) (by omega) (by omega) (w := w) (h := h) (j := l.val + 1)
    simp only [residual, rightResidual, Finset.union_empty]
    linarith
  | «suffix» l =>
    have he := right_net_demand (secondFamily T) l (hc2 l)
    rw [he, Nat.cast_add, hs l, hp l]
    have hn := net_external_demand hT (by omega) (by omega) (by omega) (by omega) (w := w) (h := h) (j := l.val + 1)
    simp only [residual, leftResidual, Finset.empty_union]
    linarith

theorem owners_nonempty {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) : (owners w h p).Nonempty := by
  have hs : ∀ l : Fin T, (leftOwners (firstFamily w h T) (.suffix l)).Nonempty := by
    intro l
    have he : leftOwners (firstFamily w h T) (.suffix l) = firstSuffixOwners w h T (l.val + 1) := by
      simp [leftOwners, firstFamily, firstSuffixOwners]
    rw [he]
    apply Finset.card_pos.mp
    have hc := firstSuffixOwners_card (by omega) (by omega) (by omega) (by omega)
      (w := w) (h := h) (T := T) (j := l.val + 1)
    have hB := auxiliaryHeight_pos T
    have hm := mul_nonneg (show (0 : ℤ) ≤ (w : ℤ) - 2 * T + (l.val + 1) - 1 by omega)
      (show (0 : ℤ) ≤ (l.val + 1) - 1 by omega)
    dsimp [sigma] at hc
    have : (0 : ℤ) < (firstSuffixOwners w h T (l.val + 1)).card := by
      push_cast at hc hm
      nlinarith
    exact_mod_cast this
  apply Finset.Nonempty.mono Finset.subset_union_left
  cases p with
  | «suffix» l => exact hs l
  | «prefix» l =>
    apply Finset.card_pos.mp
    have he := left_net_demand (firstFamily w h T) l (by simp [firstFamily])
    have hp := Finset.card_pos.mpr (hs l)
    omega


theorem geometric_height {h T : ℕ} (hT : 2 ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) : T ≤ h + 1 := by
  have hg := gamma_quadratic T
  have hm := Nat.mul_le_mul_left T hT
  nlinarith

theorem externalPool_outside {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) {x : Lattice}
    (hx : x ∈ externalPool w h p) : x ∉ projectionEnvelope w h := by
  have hh' := geometric_height hT hh
  cases p with
  | «prefix» l => exact (prefixPool_valid (by omega) (by omega) (by omega)
      (by omega) hh' (by omega) (b := 0) hx).2.2
  | «suffix» l => exact (suffixPool_valid (by omega) (by omega) (le_refl T)
      (by omega) hh' (by omega) hx).2.2

theorem external_residual_disjoint {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p q : Pattern T) :
    Disjoint (externalPool w h p) (residual w h q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact externalPool_outside hT hw hh p hx (fullBox_subset_envelope w h (residual_subset_box hw hh q hy))

theorem combinedPool_card {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    (combinedPool w h p).card = (externalPool w h p).card + (residual w h p).card :=
  Finset.card_union_of_disjoint (external_residual_disjoint hT hw hh p p)

theorem combinedPool_capacity {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (p : Pattern T) :
    (owners w h p).card ≤ (combinedPool w h p).card := by
  have hn := owner_residual_net hT hw hh p
  have hc := combinedPool_card hT hw hh p
  suffices ((owners w h p).card : ℤ) ≤ (combinedPool w h p).card by exact_mod_cast this
  rw [hc, Nat.cast_add]
  cases p with
  | «prefix» l =>
    have he := (external_pool_capacity (by omega) (by omega) (by omega) (by omega)
      (w := w) (h := h) (T := T) (j := l.val + 1)).1
    simp only [externalPool]
    dsimp at hn
    linarith
  | «suffix» l =>
    have he := (external_pool_capacity (by omega) (by omega) (by omega) (by omega)
      (w := w) (h := h) (T := T) (j := l.val + 1)).2
    simp only [externalPool]
    dsimp at hn
    linarith

theorem combinedPool_disjoint {w h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ w)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) :
    Pairwise (fun p q : Pattern T => Disjoint (combinedPool w h p) (combinedPool w h q)) := by
  intro p q hpq
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · exact Finset.disjoint_left.mp (externalPool_disjoint (by omega) hpq) hx hy
  · exact Finset.disjoint_left.mp (external_residual_disjoint hT hw hh p q) hx hy
  · exact Finset.disjoint_left.mp (external_residual_disjoint hT hw hh q p) hy hx
  · exact Finset.disjoint_left.mp (residual_disjoint hw hh hpq) hx hy

theorem private_owners_disjoint {p h T : ℕ} (hT : 2 ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (Z : Finset Lattice)
    (hZ : Z ⊆ privatePool p h T) (b : Fin (T + 1)) (q : Pattern T) :
    Disjoint (inverseSet Z b.val) (owners (p * (T + 1)) h q) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hpriv := hZ (mem_inverseSet.mp hx)
  rcases Finset.mem_union.mp hy with hy | hy
  · obtain ⟨c, hc, hy⟩ := leftOwners_hit q hy
    exact private_avoids_first hT (by omega) hc hh hpriv (mem_inverseSet.mp hy)
  · obtain ⟨c, hc, hy⟩ := rightOwners_hit q hy
    exact private_avoids_second hT (by omega) hc hh hpriv (mem_inverseSet.mp hy)

theorem residual_valid {p h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ p * (T + 1))
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (Z : Finset Lattice)
    (hZ : Z ⊆ privatePool p h T) (b : Fin (T + 1)) (q : Pattern T)
    (hq : q.occurs b.val) {x : Lattice} (hx : x ∈ residual (p * (T + 1)) h q) :
    translate b.val x ∈ tagRegion (p * (T + 1)) h T \ (primaryOne (p * (T + 1)) h T ∪ primaryTwo T ∪ Z) := by
  have hbox := residual_subset_box hw hh q hx
  refine Finset.mem_sdiff.mpr ⟨translate_envelope_mem (by omega)
    (fullBox_subset_envelope _ _ hbox), ?_⟩
  intro hhole
  rcases Finset.mem_union.mp hx with hx | hx
  · have hhit := leftResidual_hit q hx
    have hn := leftResidual_avoids (firstFamily_interval (by omega) (by omega)) hx hq
    rcases Finset.mem_union.mp hhole with hhole | hhole
    · rcases Finset.mem_union.mp hhole with hh1 | hh2
      · exact hn (mem_inverseSet.mpr hh1)
      · exact primary_families_separate hw hh hhit ⟨b.val, by omega, mem_inverseSet.mpr hh2⟩
    · obtain ⟨c, hc, hxc⟩ := hhit
      exact private_avoids_first hT (by omega) hc hh (hZ hhole) (mem_inverseSet.mp hxc)
  · have hhit := rightResidual_hit q hx
    have hn := rightResidual_avoids (secondFamily_interval T) hx hq
    rcases Finset.mem_union.mp hhole with hhole | hhole
    · rcases Finset.mem_union.mp hhole with hh1 | hh2
      · exact primary_families_separate hw hh ⟨b.val, by omega, mem_inverseSet.mpr hh1⟩ hhit
      · exact hn (mem_inverseSet.mpr hh2)
    · obtain ⟨c, hc, hxc⟩ := hhit
      exact private_avoids_second hT (by omega) hc hh (hZ hhole) (mem_inverseSet.mp hxc)

theorem combinedPool_valid {p h T : ℕ} (hT : 2 ≤ T) (hw : 4 * T ≤ p * (T + 1))
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) (Z : Finset Lattice)
    (hZ : Z ⊆ privatePool p h T) (b : Fin (T + 1)) (q : Pattern T)
    (hq : q.occurs b.val) {x : Lattice} (hx : x ∈ combinedPool (p * (T + 1)) h q) :
    translate b.val x ∈ tagRegion (p * (T + 1)) h T \ (primaryOne (p * (T + 1)) h T ∪ primaryTwo T ∪ Z) := by
  rcases Finset.mem_union.mp hx with hx | hx
  · have hv := externalPool_valid q (by omega) hq (by omega) (geometric_height hT hh) (by omega) hx
    refine Finset.mem_sdiff.mpr ⟨hv.1, ?_⟩
    intro hhits
    apply hv.2.1
    rcases Finset.mem_union.mp hhits with hhits | hhits
    · rcases Finset.mem_union.mp hhits with h1 | h2
      · exact primaryOne_subset_holeEnvelope (by omega) (by omega) h1
      · exact primaryTwo_subset_holeEnvelope hw (by omega) h2
    · exact privatePool_subset_holeEnvelope hT hh (hZ hhits)
  · exact residual_valid hT hw hh Z hZ b q hq hx

end RigidGHZ.Planar

