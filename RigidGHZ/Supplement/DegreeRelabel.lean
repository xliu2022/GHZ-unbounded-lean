module

public import RigidGHZ.Supplement.GraftDegrees

/-! Maximum codegrees are invariant under vertex relabeling. -/

@[expose] public section

namespace RigidGHZ.Supplement

open UpperBounds

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

 theorem relabelEdge_subset_iff (f : V ≃ W) (X Y : Finset V) :
    relabelEdge f X ⊆ relabelEdge f Y ↔ X ⊆ Y := by
  constructor
  · intro h v hv
    have hmem : f v ∈ relabelEdge f X := (mem_relabelEdge _ _ _).mpr (by simpa using hv)
    simpa only [mem_relabelEdge, Equiv.symm_apply_apply] using h hmem
  · intro h w hw
    exact (mem_relabelEdge _ _ _).mpr (h ((mem_relabelEdge _ _ _).mp hw))

 theorem codegree_relabel (f : V ≃ W) (H : Hypergraph V) (X : Finset V) :
    codegree (relabelHypergraph f H) (relabelEdge f X) = codegree H X := by
  classical
  have heq : (relabelHypergraph f H).filter (fun e => relabelEdge f X ⊆ e) =
      (H.filter (fun e => X ⊆ e)).image (relabelEdge f) := by
    ext e
    constructor
    · intro he
      obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp heH
      exact Finset.mem_image.mpr ⟨e0,
        Finset.mem_filter.mpr ⟨he0, (relabelEdge_subset_iff f X e0).mp hXe⟩, rfl⟩
    · intro he
      obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
      obtain ⟨heH, hXe⟩ := Finset.mem_filter.mp he0
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨e0, heH, rfl⟩,
        (relabelEdge_subset_iff f X e0).mpr hXe⟩
  change ((relabelHypergraph f H).filter _).card = _
  rw [heq, Finset.card_image_of_injective _ (relabelEdge_injective f)]
  rfl

 theorem maxDegree_relabel [Fintype V] [Fintype W] (f : V ≃ W) (H : Hypergraph V) (j : ℕ) :
    maxDegree (relabelHypergraph f H) j = maxDegree H j := by
  apply Nat.le_antisymm
  · apply maxDegree_le
    intro X hX
    have he : X = relabelEdge f (relabelEdge f.symm X) := (relabelEdge_apply_symm f X).symm
    rw [he, codegree_relabel]
    simpa only [relabelEdge_card, hX] using codegree_le_maxDegree H (relabelEdge f.symm X)
  · apply maxDegree_le
    intro X hX
    rw [← codegree_relabel f H X]
    simpa only [relabelEdge_card, hX] using codegree_le_maxDegree (relabelHypergraph f H) (relabelEdge f X)

end RigidGHZ.Supplement
