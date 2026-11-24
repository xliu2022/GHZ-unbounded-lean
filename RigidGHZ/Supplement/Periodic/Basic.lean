module

public import RigidGHZ.Supplement.GraftData
public import Mathlib.Data.Finset.Prod

/-! Actual periodic hypergraph lifts and their layers of origin. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Periodic

variable {V E L : Type*} [DecidableEq V]

/-- A simple base edge system with a proper outgoing subset for each edge. -/
structure Scheme (V E : Type*) [DecidableEq V] where
  edge : E → Finset V
  outgoing : E → Finset V
  outgoing_subset : ∀ e, outgoing e ⊆ edge e
  local_nonempty : ∀ e, (edge e \ outgoing e).Nonempty
  edge_injective : Function.Injective edge

namespace Scheme

variable (D : Scheme V E)

 def localPart (e : E) : Finset V := D.edge e \ D.outgoing e

@[simp] theorem mem_localPart (e : E) (v : V) :
    v ∈ D.localPart e ↔ v ∈ D.edge e ∧ v ∉ D.outgoing e := Finset.mem_sdiff

 def liftVertex (σ : Equiv.Perm L) (e : E) (j : L) : V ↪ (V × L) where
  toFun v := (v, if v ∈ D.outgoing e then σ j else j)
  inj' := by intro v w h; exact congrArg Prod.fst h

 def liftEdge (σ : Equiv.Perm L) (e : E) (j : L) : Finset (V × L) :=
  (D.edge e).map (D.liftVertex σ e j)

@[simp] theorem liftEdge_card (σ : Equiv.Perm L) (e : E) (j : L) :
    (D.liftEdge σ e j).card = (D.edge e).card := Finset.card_map _

@[simp] theorem mem_liftEdge (σ : Equiv.Perm L) (e : E) (j k : L) (v : V) :
    (v, k) ∈ D.liftEdge σ e j ↔ v ∈ D.edge e ∧
      k = if v ∈ D.outgoing e then σ j else j := by
  simp [liftEdge, liftVertex, eq_comm]

 theorem local_mem_liftEdge (σ : Equiv.Perm L) (e : E) (j : L) {v : V}
    (hv : v ∈ D.localPart e) : (v, j) ∈ D.liftEdge σ e j := by
  obtain ⟨he, ho⟩ := (D.mem_localPart e v).mp hv
  exact (D.mem_liftEdge σ e j j v).mpr ⟨he, by simp [ho]⟩

 theorem outgoing_mem_liftEdge (σ : Equiv.Perm L) (e : E) (j : L) {v : V}
    (hv : v ∈ D.outgoing e) : (v, σ j) ∈ D.liftEdge σ e j := by
  exact (D.mem_liftEdge σ e j (σ j) v).mpr
    ⟨D.outgoing_subset e hv, by simp [hv]⟩

 theorem projection_liftEdge (σ : Equiv.Perm L) (e : E) (j : L) :
    (D.liftEdge σ e j).image Prod.fst = D.edge e := by
  ext v
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨⟨w, k⟩, hw, rfl⟩
    exact ((D.mem_liftEdge σ e j k w).mp hw).1
  · intro hv
    exact ⟨D.liftVertex σ e j v, Finset.mem_map.mpr ⟨v, hv, rfl⟩, rfl⟩

/-- A nonempty local part identifies the origin layer even at period one. -/
theorem liftEdge_injective (σ : Equiv.Perm L) :
    Function.Injective (fun p : E × L => D.liftEdge σ p.1 p.2) := by
  rintro ⟨e, j⟩ ⟨f, k⟩ h
  change D.liftEdge σ e j = D.liftEdge σ f k at h
  have hef : e = f := D.edge_injective (by
    have hh := congrArg (fun S : Finset (V × L) => S.image Prod.fst) h
    simpa only [D.projection_liftEdge] using hh)
  subst f
  obtain ⟨v, hv⟩ := D.local_nonempty e
  have hmem := D.local_mem_liftEdge σ e j hv
  rw [h] at hmem
  have hj := ((D.mem_liftEdge σ e k j v).mp hmem).2
  have hno := (Finset.mem_sdiff.mp hv).2
  have hjk : j = k := by simpa only [if_neg hno] using hj
  exact Prod.ext rfl hjk

 theorem edge_eq_of_lift_eq (σ : Equiv.Perm L) {e f : E} {j k : L}
    (h : D.liftEdge σ e j = D.liftEdge σ f k) : e = f := by
  have hp : (e, j) = (f, k) := D.liftEdge_injective σ h
  exact congrArg Prod.fst hp

variable [Fintype E] [Fintype L] [DecidableEq E] [DecidableEq L]

 def graph (σ : Equiv.Perm L) : Hypergraph (V × L) :=
  Finset.univ.image (fun p : E × L => D.liftEdge σ p.1 p.2)

 def selection (σ : Equiv.Perm L) (A : L → Finset E) : Hypergraph (V × L) :=
  Finset.univ.biUnion (fun j => (A j).image (fun e => D.liftEdge σ e j))

 def take (σ : Equiv.Perm L) (M : Hypergraph (V × L)) (j : L) : Finset E :=
  Finset.univ.filter (fun e => D.liftEdge σ e j ∈ M)

 theorem selection_subset (σ : Equiv.Perm L) (A : L → Finset E) : D.selection σ A ⊆ D.graph σ := by
  intro g hg
  obtain ⟨j, hj, hg⟩ := Finset.mem_biUnion.mp hg
  obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hg
  exact Finset.mem_image.mpr ⟨(e, j), Finset.mem_univ _, rfl⟩

 theorem mem_selection (σ : Equiv.Perm L) (A : L → Finset E) (g : Finset (V × L)) :
    g ∈ D.selection σ A ↔ ∃ j e, e ∈ A j ∧ D.liftEdge σ e j = g := by
  simp [selection]

@[simp] theorem liftEdge_mem_selection (σ : Equiv.Perm L) (A : L → Finset E) (e : E) (j : L) :
    D.liftEdge σ e j ∈ D.selection σ A ↔ e ∈ A j := by
  constructor
  · intro h
    obtain ⟨k, f, hf, hfe⟩ := (D.mem_selection σ A _).mp h
    have hpair : (f, k) = (e, j) := D.liftEdge_injective σ hfe
    have hef : f = e := congrArg Prod.fst hpair
    have hkj : k = j := congrArg Prod.snd hpair
    simpa only [hef, hkj] using hf
  · intro he
    exact (D.mem_selection σ A _).mpr ⟨j, e, he, rfl⟩

@[simp] theorem take_selection (σ : Equiv.Perm L) (A : L → Finset E) :
    D.take σ (D.selection σ A) = A := by
  funext j
  ext e
  simp [take]

 theorem selection_take (σ : Equiv.Perm L) {M : Hypergraph (V × L)} (hM : M ⊆ D.graph σ) :
    D.selection σ (D.take σ M) = M := by
  ext g
  constructor
  · intro hg
    obtain ⟨j, e, he, rfl⟩ := (D.mem_selection σ _ _).mp hg
    exact (Finset.mem_filter.mp he).2
  · intro hg
    obtain ⟨⟨e, j⟩, hp, rfl⟩ := Finset.mem_image.mp (hM hg)
    exact (D.mem_selection σ _ _).mpr ⟨j, e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hg⟩, rfl⟩

 theorem selection_injective (σ : Equiv.Perm L) : Function.Injective (D.selection σ) := by
  intro A B h
  have hh := congrArg (D.take σ) h
  simpa only [D.take_selection] using hh

 theorem graph_uniform (σ : Equiv.Perm L) {r : ℕ} (h : ∀ e, (D.edge e).card = r) :
    Uniform (D.graph σ) r := by
  intro g hg
  obtain ⟨⟨e, j⟩, he, rfl⟩ := Finset.mem_image.mp hg
  simpa using h e

variable [Fintype V]

 def localVertices (A : Finset E) : Finset V := A.biUnion D.localPart
 def output (A : Finset E) : Finset V := A.biUnion D.outgoing
 def input (A : Finset E) : Finset V := Finset.univ \ D.localVertices A
 def allOutgoing : Finset V := Finset.univ.biUnion D.outgoing

 def LocalConfig (A : Finset E) : Prop :=
  (∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.localPart e) (D.localPart f)) ∧
  (∀ e ∈ A, ∀ f ∈ A, e ≠ f → Disjoint (D.outgoing e) (D.outgoing f)) ∧
  D.input A ⊆ D.allOutgoing

 def PeriodicConfig (σ : Equiv.Perm L) (A : L → Finset E) : Prop :=
  (∀ j, D.LocalConfig (A j)) ∧ ∀ j, D.output (A j) = D.input (A (σ j))

@[simp] theorem mem_input (A : Finset E) (v : V) :
    v ∈ D.input A ↔ ∀ e ∈ A, v ∉ D.localPart e := by
  simp [input, localVertices]

@[simp] theorem mem_output (A : Finset E) (v : V) :
    v ∈ D.output A ↔ ∃ e ∈ A, v ∈ D.outgoing e := by simp [output]

end Scheme
end RigidGHZ.Supplement.Periodic
