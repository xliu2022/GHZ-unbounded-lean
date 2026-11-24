module

public import RigidGHZ.Construction.OwnerBlockModel
public import RigidGHZ.Construction.RectanglePools

@[expose] public section

namespace RigidGHZ.Rectangle

open RectangleAnchors

 theorem Pattern.exists_occurs {T : ℕ} (p : Pattern T) :
    ∃ b : Fin (T + 1), p.occurs b.val := by
  cases p with
  | full => exact ⟨0, trivial⟩
  | «prefix» l => exact ⟨0, Nat.zero_le _⟩
  | «suffix» l => exact ⟨l.succ, Nat.lt_succ_self _⟩

 theorem externalPool_outside {A B H T : ℕ} (i : Fin (T + 1)) (p : Pattern T)
    {x : Point3} (hx : x ∈ externalPool A B H T i.val p) :
    x ∉ projectionEnvelope A B H := by
  obtain ⟨b, hb⟩ := p.exists_occurs
  exact (externalPool_valid (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ b.isLt) p hb hx).2

 theorem projection_translate_in_tagBox {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    {x : Point3} (hx : x ∈ projectionEnvelope A B H) :
    rowTranslate i b x ∈ tagBox A B H T := by
  have hgi := gamma_mono hi
  have hgb := gamma_mono hb
  simp only [projectionEnvelope, tagBox, box, rowTranslate, Finset.mem_product, Finset.mem_Ico] at hx ⊢
  omega

variable {K : Type*} [Fintype K] [DecidableEq K] {A B H T P : ℕ}
    (r : K → PrimaryRectangle) (X Z : Finset Point3)
    (hprimary : ∀ k, (r k).plane % (T + 1) = 0)
    (hsep : Pairwise (fun k l => (r k).Separated T (r l)))
    (hgrid : ∀ z ∈ Z, z.1 % (T + 1 : ℤ) = 0 ∧ z.2.1 % (T + 1 : ℤ) = 0)
    (hplanes : ∀ k, (r k).plane ≤ P)
    (hZafter : ∀ z ∈ Z, (P : ℤ) + T + 1 ≤ z.1)
    (hownerX : ∀ (i : Fin (T + 1)) (p : Pattern T), ownerBlock r i p ⊆ X)
    (hX : X ⊆ projectionEnvelope A B H)

def combinedPool (i : Fin (T + 1)) (p : Pattern T) : Finset Point3 :=
  externalPool A B H T i.val p ∪ residualPool r i p

include hprimary hsep hownerX hX

 theorem residualPool_inside (i : Fin (T + 1)) (p : Pattern T) :
    residualPool r i p ⊆ projectionEnvelope A B H :=
  (residualPool_subset_full r hprimary hsep i p).trans ((hownerX i Pattern.full).trans hX)

 theorem external_residual_disjoint (i : Fin (T + 1)) (p q : Pattern T) :
    Disjoint (externalPool A B H T i.val p) (residualPool r i q) := by
  apply Finset.disjoint_left.mpr
  intro x he hr
  exact externalPool_outside i p he (residualPool_inside r X hprimary hsep hownerX hX i q hr)

 theorem combinedPool_card (i : Fin (T + 1)) (p : Pattern T) :
    (combinedPool (A := A) (B := B) (H := H) r i p).card =
      externalSupply A B H T p + (residualPool r i p).card := by
  rw [combinedPool, Finset.card_union_of_disjoint
    (external_residual_disjoint r X hprimary hsep hownerX hX i p p), externalPool_card]

 theorem combinedPool_disjoint_when_used (i : Fin (T + 1)) (p q : Pattern T)
    (b : ℕ) (hpq : p ≠ q) (hp : p.occurs b) (hq : q.occurs b) :
    Disjoint (combinedPool (A := A) (B := B) (H := H) r i p)
      (combinedPool (A := A) (B := B) (H := H) r i q) := by
  apply Finset.disjoint_left.mpr
  intro x hxp hxq
  rcases Finset.mem_union.mp hxp with he | hr <;> rcases Finset.mem_union.mp hxq with he' | hr'
  · exact Finset.disjoint_left.mp (externalPool_pairwise (Nat.le_of_lt_succ i.isLt) hpq) he he'
  · exact Finset.disjoint_left.mp
      (external_residual_disjoint r X hprimary hsep hownerX hX i p q) he hr'
  · exact Finset.disjoint_left.mp
      (external_residual_disjoint r X hprimary hsep hownerX hX i q p) he' hr
  · exact Finset.disjoint_left.mp
      (residualPool_disjoint_when_used r hprimary hsep i p q b hpq hp hq) hr hr'

include hgrid hplanes hZafter

/-- Every combined anchor is an available tag on every exit in its pattern. -/
theorem combinedPool_valid
    (hholes : primaryHoles r ∪ Z ⊆ holeBox A B H T)
    (i b : Fin (T + 1)) (p : Pattern T) (hp : p.occurs b.val)
    {x : Point3} (hx : x ∈ combinedPool (A := A) (B := B) (H := H) r i p) :
    rowTranslate i.val b.val x ∈ tagBox A B H T \ (primaryHoles r ∪ Z) := by
  rcases Finset.mem_union.mp hx with he | hr
  · exact externalPool_avoids_holes (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ b.isLt)
      p hp hholes he
  · apply Finset.mem_sdiff.mpr
    refine ⟨projection_translate_in_tagBox (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ b.isLt)
      (residualPool_inside r X hprimary hsep hownerX hX i p hr), ?_⟩
    intro hh
    rcases Finset.mem_union.mp hh with hprimaryHit | hprivateHit
    · exact residualPool_avoids_primary r hprimary hsep i b p hp hr hprimaryHit
    · have hpriv := (mem_privateBlock_iff Z i.val b.val x).mpr hprivateHit
      have hfull := residualPool_subset_full r hprimary hsep i p hr
      exact Finset.disjoint_left.mp
        (private_ownerBlock_disjoint r Z hprimary hsep hgrid hplanes hZafter i b i Pattern.full)
        hpriv hfull

end RigidGHZ.Rectangle
