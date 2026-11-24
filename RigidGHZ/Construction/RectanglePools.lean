module

public import RigidGHZ.Construction.RectangleAnchors
public import RigidGHZ.Construction.OwnerPatterns

@[expose] public section

namespace RigidGHZ.RectangleAnchors

open RigidGHZ.Rectangle

def externalPool (A B H T i : ℕ) : Pattern T → Finset Lattice
  | .full => fullPool A B H T i
  | .prefix l => prefixPool A B H T i l.val
  | .suffix l => suffixPool A B H i l.val

def externalSupply (A B H T : ℕ) : Pattern T → ℕ
  | .full => T * B * H + A * B * gamma T
  | .prefix l => A * H + A * B * l.val
  | .suffix l => A * H + A * B * l.val

theorem externalPool_card (A B H T i : ℕ) (p : Pattern T) :
    (externalPool A B H T i p).card = externalSupply A B H T p := by
  cases p with
  | full => exact fullPool_card A B H T i
  | «prefix» l => exact prefixPool_card l.isLt
  | «suffix» l => exact suffixPool_card A B H i l.val

theorem externalPool_pairwise {A B H T i : ℕ} (hi : i ≤ T) :
    Pairwise (fun p q : Pattern T =>
      Disjoint (externalPool A B H T i p) (externalPool A B H T i q)) := by
  intro p q hpq
  cases p with
  | full =>
    cases q with
    | full => exact (hpq rfl).elim
    | «prefix» l => exact fullPool_disjoint_prefixPool hi l.isLt
    | «suffix» l => exact fullPool_disjoint_suffixPool A B H T i l.val
  | «prefix» l =>
    cases q with
    | full => exact (fullPool_disjoint_prefixPool hi l.isLt).symm
    | «prefix» j =>
      apply prefixPool_disjoint_prefixPool l.isLt j.isLt
      intro h
      exact hpq (congrArg Pattern.prefix (Fin.ext h))
    | «suffix» j => exact prefixPool_disjoint_suffixPool hi l.isLt
  | «suffix» l =>
    cases q with
    | full => exact (fullPool_disjoint_suffixPool A B H T i l.val).symm
    | «prefix» j => exact (prefixPool_disjoint_suffixPool hi j.isLt).symm
    | «suffix» j =>
      apply suffixPool_disjoint_suffixPool
      intro h
      exact hpq (congrArg Pattern.suffix (Fin.ext h))

theorem externalPool_valid {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (p : Pattern T) (hp : p.occurs b) {z : Lattice}
    (hz : z ∈ externalPool A B H T i p) :
    translate i b z ∈ tagBox A B H T \ holeBox A B H T ∧
      z ∉ projectionEnvelope A B H := by
  cases p with
  | full => exact fullPool_valid hi hb hz
  | «prefix» l => exact prefixPool_valid hi l.isLt hp hz
  | «suffix» l => exact suffixPool_valid hi hb hp hz

/-- Removing any collection of holes inside the prescribed interior box leaves
every allowed external-anchor translate available. -/
theorem externalPool_avoids_holes {A B H T i b : ℕ} (hi : i ≤ T) (hb : b ≤ T)
    (p : Pattern T) (hp : p.occurs b) {holes : Finset Lattice}
    (hholes : holes ⊆ holeBox A B H T) {z : Lattice}
    (hz : z ∈ externalPool A B H T i p) :
    translate i b z ∈ tagBox A B H T \ holes := by
  obtain ⟨h, _⟩ := externalPool_valid hi hb p hp hz
  rw [Finset.mem_sdiff] at h ⊢
  exact ⟨h.1, fun hh => h.2 (hholes hh)⟩

end RigidGHZ.RectangleAnchors
