module

public import RigidGHZ.Construction.PlanarPrivate
public import RigidGHZ.Construction.PlanarPatterns

/-! The planar external pools are disjoint and provide valid tags outside all holes. -/

@[expose] public section

namespace RigidGHZ.Planar

open RigidGHZ.Rectangle
open scoped Finset

def holeEnvelope (w h T : ℕ) : Finset Lattice := box T w (gamma T) h

def externalPool (w h : ℕ) {T : ℕ} : Pattern T → Finset Lattice
  | .prefix l => prefixPool w h T (l.val + 1)
  | .suffix l => suffixPool w h T (l.val + 1)

theorem primaryOne_subset_holeEnvelope {w h T : ℕ} (hw : 2 * T ≤ w) (hh : 2 * gamma T ≤ h) :
    primaryOne w h T ⊆ holeEnvelope w h T := by
  intro x hx
  simp only [primaryOne, holeEnvelope, box, Finset.mem_union, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  rcases hx with hx | hx <;> omega

theorem primaryTwo_subset_holeEnvelope {w h T : ℕ} (hw : 4 * T ≤ w)
    (hh : 3 * gamma T + auxiliaryHeight T ≤ h) : primaryTwo T ⊆ holeEnvelope w h T := by
  intro x hx
  simp only [primaryTwo, holeEnvelope, box, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

theorem privatePool_subset_holeEnvelope {p h T : ℕ} (hT : 2 ≤ T)
    (hh : 4 * gamma T + auxiliaryHeight T ≤ h) : privatePool p h T ⊆ holeEnvelope (p * (T + 1)) h T := by
  intro x hx
  have he := private_inverse_envelope hT (Nat.zero_le T) hh (x := x) (by simpa [translate] using hx)
  simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico] at he ⊢
  push_cast at he ⊢
  omega

theorem prefixPool_valid {w h T j b : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hb : b < j) (hw : 2 * T ≤ w) (hh : T ≤ h + 1) (hD : gamma T ≤ h)
    {x : Lattice} (hx : x ∈ prefixPool w h T j) :
    translate b x ∈ tagRegion w h T ∧ translate b x ∉ holeEnvelope w h T ∧
      x ∉ projectionEnvelope w h := by
  rcases Finset.mem_union.mp hx with hx | hx
  · obtain ⟨hy, hn, hxw⟩ := prefixColumn_valid (by omega) hj hjT hb hw hh hx
    refine ⟨hy, ?_, hn⟩
    simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega
  · obtain ⟨hy, hn, hyh⟩ := prefixStrip_valid hj hjT hb hD hx
    refine ⟨hy, ?_, hn⟩
    simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega

theorem suffixPool_valid {w h T j b : ℕ} (hj : 1 ≤ j) (hjb : j ≤ b) (hbT : b ≤ T)
    (hw : 2 * T ≤ w) (hh : T ≤ h + 1) (hD : gamma T ≤ h)
    {x : Lattice} (hx : x ∈ suffixPool w h T j) :
    translate b x ∈ tagRegion w h T ∧ translate b x ∉ holeEnvelope w h T ∧
      x ∉ projectionEnvelope w h := by
  rcases Finset.mem_union.mp hx with hx | hx
  · rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨hy, hn, hxT⟩ := suffixColumn_valid hj (by omega) hjb hbT (by omega) hh hx
      refine ⟨hy, ?_, hn⟩
      simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico]
      omega
    · obtain ⟨hy, hn, hyD⟩ := suffixStrip_valid hj hjb hbT hD hx
      refine ⟨hy, ?_, hn⟩
      simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico]
      omega
  · obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
    obtain ⟨hy, hn, hyD⟩ := lowerColumn_valid (Finset.mem_range.mp ha) hj hjb hbT hw hh hx
    refine ⟨hy, ?_, hn⟩
    simp only [holeEnvelope, box, Finset.mem_product, Finset.mem_Ico]
    omega

theorem externalPool_valid {w h T b : ℕ} (p : Pattern T) (hb : b ≤ T) (hp : p.occurs b)
    (hw : 2 * T ≤ w) (hh : T ≤ h + 1) (hD : gamma T ≤ h)
    {x : Lattice} (hx : x ∈ externalPool w h p) :
    translate b x ∈ tagRegion w h T ∧ translate b x ∉ holeEnvelope w h T ∧
      x ∉ projectionEnvelope w h := by
  cases p with
  | «prefix» l => exact prefixPool_valid (by omega) (by omega) (by change b ≤ l.val at hp; omega) hw hh hD hx
  | «suffix» l => exact suffixPool_valid (by omega) (by exact hp) hb hw hh hD hx

theorem lowerPool_bounds {w T j : ℕ} {x : Lattice} (hx : x ∈ lowerPool w T j) :
    (w : ℤ) - T ≤ x.1 ∧ x.1 < w ∧ x.2 < 0 := by
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  have ha' := Finset.mem_range.mp ha
  have hr := rise_nonneg a (j - 1)
  simp only [lowerColumn, box, Finset.mem_product, Finset.mem_Ico] at hx
  omega

theorem prefix_suffix_disjoint {w h T j k : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hk : 1 ≤ k) (hkT : k ≤ T) (hw : 2 * T ≤ w) :
    Disjoint (prefixPool w h T j) (suffixPool w h T k) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  have hg := gamma_int_mono hjT
  rcases Finset.mem_union.mp hx with hx | hx
  · simp only [prefixColumn, box, Finset.mem_product, Finset.mem_Ico] at hx
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [Finset.mem_union, suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hy
      rcases hy with hy | hy <;> omega
    · have hy' := lowerPool_bounds hy
      omega
  · simp only [prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx
    rcases Finset.mem_union.mp hy with hy | hy
    · simp only [Finset.mem_union, suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hy
      rcases hy with hy | hy <;> omega
    · have hy' := lowerPool_bounds hy
      omega

theorem prefixPool_disjoint {w h T j k : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hk : 1 ≤ k) (hkT : k ≤ T) (hjk : j ≠ k) :
    Disjoint (prefixPool w h T j) (prefixPool w h T k) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · simp only [prefixColumn, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  · simp only [prefixColumn, prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  · simp only [prefixColumn, prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    omega
  · simp only [prefixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
    rcases lt_or_gt_of_ne hjk with h | h
    · have hg := gamma_int_mono (show j ≤ k - 1 by omega)
      omega
    · have hg := gamma_int_mono (show k ≤ j - 1 by omega)
      omega

theorem lowerPool_disjoint {w T j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) (hjk : j ≠ k) :
    Disjoint (lowerPool w T j) (lowerPool w T k) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨a, ha, hx⟩ := Finset.mem_biUnion.mp hx
  obtain ⟨c, hc, hy⟩ := Finset.mem_biUnion.mp hy
  simp only [lowerColumn, box, Finset.mem_product, Finset.mem_Ico] at hx hy
  have hac : a = c := by omega
  subst c
  rcases lt_or_gt_of_ne hjk with h | h
  · have hr := rise_mono a (show j ≤ k - 1 by omega)
    omega
  · have hr := rise_mono a (show k ≤ j - 1 by omega)
    omega

theorem suffixPool_disjoint {w h T j k : ℕ} (hj : 1 ≤ j) (hjT : j ≤ T)
    (hk : 1 ≤ k) (hkT : k ≤ T) (hjk : j ≠ k) (hw : 2 * T ≤ w) :
    Disjoint (suffixPool w h T j) (suffixPool w h T k) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  rcases Finset.mem_union.mp hx with hx | hx <;> rcases Finset.mem_union.mp hy with hy | hy
  · simp only [Finset.mem_union] at hx hy
    rcases hx with hx | hx <;> rcases hy with hy | hy
    · simp only [suffixColumn, box, Finset.mem_product, Finset.mem_Ico] at hx hy
      omega
    · simp only [suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
      omega
    · simp only [suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
      omega
    · simp only [suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx hy
      rcases lt_or_gt_of_ne hjk with h | h
      · have hg := gamma_int_mono (show j ≤ k - 1 by omega)
        omega
      · have hg := gamma_int_mono (show k ≤ j - 1 by omega)
        omega
  · have hy' := lowerPool_bounds hy
    simp only [Finset.mem_union, suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hx
    rcases hx with hx | hx <;> omega
  · have hx' := lowerPool_bounds hx
    simp only [Finset.mem_union, suffixColumn, suffixStrip, box, Finset.mem_product, Finset.mem_Ico] at hy
    rcases hy with hy | hy <;> omega
  · exact Finset.disjoint_left.mp (lowerPool_disjoint hj hk hjk) hx hy

theorem externalPool_disjoint {w h T : ℕ} (hw : 2 * T ≤ w) :
    Pairwise (fun p q : Pattern T => Disjoint (externalPool w h p) (externalPool w h q)) := by
  intro p q hpq
  cases p with
  | «prefix» l =>
    cases q with
    | «prefix» k =>
      apply prefixPool_disjoint (by omega) (by omega) (by omega) (by omega)
      intro h
      exact hpq (congrArg Pattern.prefix (Fin.ext (by omega)))
    | «suffix» k => exact prefix_suffix_disjoint (by omega) (by omega) (by omega) (by omega) hw
  | «suffix» l =>
    cases q with
    | «prefix» k => exact (prefix_suffix_disjoint (by omega) (by omega) (by omega) (by omega) hw).symm
    | «suffix» k =>
      apply suffixPool_disjoint (by omega) (by omega) (by omega) (by omega) ?_ hw
      intro h
      exact hpq (congrArg Pattern.suffix (Fin.ext (by omega)))

end RigidGHZ.Planar
