module

public import RigidGHZ.Selector.ForcedContraction
public import RigidGHZ.Selector.ExpandedDoubleComb

/-! One-row double comb with no full-row owner chain. The original forced hub
is deleted; its successor becomes the unique new hub. -/

@[expose] public section

namespace RigidGHZ.Selector.PlanarComb

open Equiv Equiv.Perm BlockExpansion

abbrev Ambient (T : ℕ) := DoubleComb.Vertex Unit T
abbrev Vertex (T : ℕ) := ForcedContraction.Remaining (DoubleComb.Vertex.hub : Ambient T)

def hub (T : ℕ) : Vertex T := ⟨.upper () 0, by simp⟩
def suffix {T : ℕ} (a : Fin T) : Vertex T := ⟨.upper () ⟨a.val + 1, by omega⟩, by simp⟩
def branch {T : ℕ} (b : Fin (T + 1)) : Vertex T := ⟨.branch () b, by simp⟩
def prefixBlock {T : ℕ} (a : Fin T) : Vertex T := ⟨.lower () a, by simp⟩

variable {T : ℕ}

theorem forced_edge (b : Fin (T + 1)) :
    DoubleComb.routePerm () b DoubleComb.Vertex.hub = (hub T).val := by
  exact DoubleComb.routePerm_apply_onRoute () b _ trivial

noncomputable def routePerm (b : Fin (T + 1)) : Equiv.Perm (Vertex T) :=
  ForcedContraction.contracted _ (hub T).val (DoubleComb.routePerm () b) (forced_edge b)

def Arc (x y : Vertex T) : Prop :=
  ForcedContraction.Arc DoubleComb.Arc _ (hub T).val x y

theorem routePerm_cover (b : Fin (T + 1)) : ∀ x, Arc x (routePerm b x) :=
  ForcedContraction.contracted_cover DoubleComb.Arc _ (hub T).val
    (DoubleComb.routePerm () b) (forced_edge b) (DoubleComb.routePerm_cover () b)

theorem cover_complete (q : Equiv.Perm (Vertex T)) (hq : ∀ x, Arc x (q x)) :
    ∃ b, q = routePerm b := by
  apply ForcedContraction.complete DoubleComb.Arc _ (hub T).val
    (by exact ⟨(), rfl⟩) (fun b => DoubleComb.routePerm () b) forced_edge ?_ q hq
  intro Q hQ
  obtain ⟨i, b, hb⟩ := DoubleComb.cover_complete Q hQ
  cases i
  exact ⟨b, hb⟩

theorem selector_complete (q : Equiv.Perm (Vertex T))
    (hq : ∀ x, ∃ b, q x = routePerm b x) : ∃ b, q = routePerm b := by
  apply cover_complete q
  intro x
  obtain ⟨b, hb⟩ := hq x
  rw [hb]
  exact routePerm_cover b x

theorem no_two_cycle (b : Fin (T + 1)) :
    DoubleComb.routePerm () b (hub T).val ≠ DoubleComb.Vertex.hub := by
  intro he
  have hc := DoubleComb.routePerm_cover () b (hub T).val
  rw [he] at hc
  simpa [hub, DoubleComb.Arc] using hc

theorem routePerm_moves_iff (b : Fin (T + 1)) (x : Vertex T) :
    routePerm b x ≠ x ↔ DoubleComb.OnRoute () b x.val := by
  exact (ForcedContraction.contracted_moves_iff _ _ (DoubleComb.routePerm () b)
    (forced_edge b) (no_two_cycle b) x).trans (DoubleComb.routePerm_moves_iff () b x.val)

@[simp] theorem hub_moves (b : Fin (T + 1)) : routePerm b (hub T) ≠ hub T :=
  (routePerm_moves_iff b _).mpr ⟨rfl, Nat.zero_le _⟩

@[simp] theorem suffix_moves (b : Fin (T + 1)) (a : Fin T) :
    routePerm b (suffix a) ≠ suffix a ↔ a.val < b.val := by
  rw [routePerm_moves_iff]
  simp only [suffix, DoubleComb.OnRoute, true_and]
  omega

@[simp] theorem prefix_moves (b : Fin (T + 1)) (a : Fin T) :
    routePerm b (prefixBlock a) ≠ prefixBlock a ↔ b.val ≤ a.val := by
  rw [routePerm_moves_iff]
  simp [prefixBlock, DoubleComb.OnRoute]

@[simp] theorem branch_moves (b c : Fin (T + 1)) :
    routePerm b (branch c) ≠ branch c ↔ c = b := by
  rw [routePerm_moves_iff]
  simp [branch, DoubleComb.OnRoute]

variable (n : Vertex T → ℕ)

noncomputable def expandedPerm (b : Fin (T + 1)) : Equiv.Perm (Point n) :=
  lift n (routePerm b)

theorem expandedPerm_cover (b : Fin (T + 1)) :
    ∀ x, BlockExpansion.Arc n Arc x (expandedPerm n b x) :=
  lift_cover n Arc (routePerm b) (routePerm_cover b)

theorem expanded_cover_complete (Q : Equiv.Perm (Point n))
    (hQ : ∀ x, BlockExpansion.Arc n Arc x (Q x)) :
    ∃ b, Q = expandedPerm n b := by
  obtain ⟨b, hb⟩ := cover_complete (compress Q hQ) (compress_cover Q hQ)
  refine ⟨b, ?_⟩
  rw [← lift_compress Q hQ, hb]
  rfl

theorem expanded_selector_complete (Q : Equiv.Perm (Point n))
    (hQ : ∀ x, ∃ b, Q x = expandedPerm n b x) :
    ∃ b, Q = expandedPerm n b := by
  apply expanded_cover_complete n Q
  intro x
  obtain ⟨b, hb⟩ := hQ x
  rw [hb]
  exact expandedPerm_cover n b x

theorem expandedPerm_moves_iff (b : Fin (T + 1)) (x : Point n) :
    expandedPerm n b x ≠ x ↔ DoubleComb.OnRoute () b x.1.val :=
  (lift_moves_iff n (routePerm b) x).trans (routePerm_moves_iff b x.1)

end RigidGHZ.Selector.PlanarComb
