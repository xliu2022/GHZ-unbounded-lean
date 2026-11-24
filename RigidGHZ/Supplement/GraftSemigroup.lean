module

public import RigidGHZ.Supplement.Grafting

/-! Repeated grafting, with simultaneous maximum-codegree bounds. -/

@[expose] public section

namespace RigidGHZ.Supplement

open UpperBounds

/-- A canonical balanced rigid hypergraph with a bound at every positive degree order. -/
def BoundedRigid (r m d : ℕ) (b : ℕ → ℕ) : Prop :=
  ∃ H : Hypergraph (Fin r × Fin m), Uniform H r ∧ BalancedPartite H r m ∧ IsRigid H d ∧
    ∀ j : ℕ, 1 ≤ j → maxDegree H j ≤ b j

/-- The analogous existence statement without a multipartite requirement. -/
def BoundedUnrestricted (r m d : ℕ) (b : ℕ → ℕ) : Prop :=
  ∃ H : Hypergraph (Fin (r * m)), Uniform H r ∧ IsRigid H d ∧
    ∀ j : ℕ, 1 ≤ j → maxDegree H j ≤ b j

 theorem maxDegree_rigid_le {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {d j : ℕ} (hR : IsRigid H d) (hj : 1 ≤ j) : maxDegree H j ≤ d := by
  obtain ⟨R⟩ := hR
  apply maxDegree_le
  intro X hX
  have hp : X.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨v, hv⟩ := hp
  have hsub : H.filter (fun e => X ⊆ e) ⊆ H.filter (fun e => v ∈ e) := by
    intro e he
    obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he
    exact Finset.mem_filter.mpr ⟨heH, hXe hv⟩
  have hcard := Finset.card_le_card hsub
  change codegree H X ≤ degree H v at hcard
  have hvdegree : degree H v = d := by simpa only [Fintype.card_fin] using R.regular v
  exact hcard.trans_eq hvdegree

 def pairBounds (d c j : ℕ) : ℕ := if j = 2 then c else d

/-- For a rigid hypergraph, a pair bound supplies all other positive-order
bounds automatically through regularity. -/
theorem boundedRigid_of_pair_bound {V : Type*} [Fintype V] [DecidableEq V]
    {H : Hypergraph V} {r m d c : ℕ} (hU : Uniform H r) (hP : BalancedPartite H r m)
    (hR : IsRigid H d) (h2 : maxDegree H 2 ≤ c) : BoundedRigid r m d (pairBounds d c) := by
  classical
  obtain ⟨e, he⟩ := hP.canonical
  refine ⟨relabelHypergraph e H, hU.relabel e, ?_, hR.relabel e, ?_⟩
  · simpa only [Fintype.card_fin] using balancedPartite_of_transversal _ he
  · intro j hj
    rw [maxDegree_relabel]
    by_cases h : j = 2
    · simpa [pairBounds, h] using h2
    · simpa only [pairBounds, if_neg h] using maxDegree_rigid_le hR hj

namespace BoundedRigid

variable {r m q d : ℕ} {b : ℕ → ℕ}

 theorem graft (h : BoundedRigid r m d b) (s : BoundedRigid r q d b)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) : BoundedRigid r (m + q - 1) d b := by
  obtain ⟨H, hUH, hPH, ⟨RH⟩, hDH⟩ := h
  obtain ⟨S, hUS, hPS, ⟨RS⟩, hDS⟩ := s
  obtain ⟨G, hUG, hPG, ⟨RG⟩, hDG⟩ := grafting_balanced hr hm hq hPH RH hPS RS
  refine ⟨G, hUG, hPG, ⟨RG⟩, ?_⟩
  intro j hj
  exact (hDG j hj).trans (max_le (hDH j hj) (hDS j hj))

/-- Grafting a finite list increases the part size by the sum of `q-1`. -/
theorem graft_list (h : BoundedRigid r m d b) (qs : List ℕ)
    (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hs : ∀ q ∈ qs, 1 ≤ q ∧ BoundedRigid r q d b) :
    BoundedRigid r (m + (qs.map (fun q => q - 1)).sum) d b := by
  induction qs generalizing m with
  | nil => simpa using h
  | cons q qs ih =>
    have hq := hs q (List.mem_cons_self)
    have hfirst := h.graft hq.2 hr hm hq.1
    have hrest := ih hfirst (by omega : 1 ≤ m + q - 1)
      (fun p hp => hs p (List.mem_cons_of_mem _ hp))
    have he : (m + q - 1) + (qs.map (fun q => q - 1)).sum =
        m + ((q :: qs).map (fun q => q - 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rwa [he] at hrest

/-- Supplemental Corollary S3.2 for a nonempty collection of balanced grafts. -/
theorem semigroup (qs : List ℕ) (hne : qs ≠ []) (hr : 1 ≤ r)
    (hs : ∀ q ∈ qs, 1 ≤ q ∧ BoundedRigid r q d b) :
    BoundedRigid r (1 + (qs.map (fun q => q - 1)).sum) d b := by
  cases qs with
  | nil => exact (hne rfl).elim
  | cons q qs =>
    have hq := hs q (List.mem_cons_self)
    have h := hq.2.graft_list qs hr hq.1 (fun p hp => hs p (List.mem_cons_of_mem _ hp))
    have he : q + (qs.map (fun q => q - 1)).sum =
        1 + ((q :: qs).map (fun q => q - 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rwa [he] at h

end BoundedRigid

namespace BoundedUnrestricted

variable {r m q d : ℕ} {b : ℕ → ℕ}

 theorem graft (h : BoundedUnrestricted r m d b) (s : BoundedRigid r q d b)
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hq : 1 ≤ q) : BoundedUnrestricted r (m + q - 1) d b := by
  obtain ⟨H, hUH, ⟨RH⟩, hDH⟩ := h
  obtain ⟨S, hUS, hPS, ⟨RS⟩, hDS⟩ := s
  obtain ⟨G, hUG, ⟨RG⟩, hDG⟩ := grafting hr hm hq (by simp) hUH RH hPS RS
  refine ⟨G, hUG, ⟨RG⟩, ?_⟩
  intro j hj
  exact (hDG j hj).trans (max_le (hDH j hj) (hDS j hj))

/-- Unrestricted matching size increases by the same additive semigroup. -/
theorem graft_list (h : BoundedUnrestricted r m d b) (qs : List ℕ)
    (hr : 1 ≤ r) (hm : 1 ≤ m)
    (hs : ∀ q ∈ qs, 1 ≤ q ∧ BoundedRigid r q d b) :
    BoundedUnrestricted r (m + (qs.map (fun q => q - 1)).sum) d b := by
  induction qs generalizing m with
  | nil => simpa using h
  | cons q qs ih =>
    have hq := hs q (List.mem_cons_self)
    have hfirst := h.graft hq.2 hr hm hq.1
    have hrest := ih hfirst (by omega : 1 ≤ m + q - 1)
      (fun p hp => hs p (List.mem_cons_of_mem _ hp))
    have he : (m + q - 1) + (qs.map (fun q => q - 1)).sum =
        m + ((q :: qs).map (fun q => q - 1)).sum := by
      simp only [List.map_cons, List.sum_cons]
      omega
    rwa [he] at hrest

end BoundedUnrestricted
end RigidGHZ.Supplement
