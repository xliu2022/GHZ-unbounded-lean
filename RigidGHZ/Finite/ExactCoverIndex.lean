module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed

/-! Index-level table checks avoid repeatedly comparing whole finite edge sets.
All conclusions remain statements about the ordinary hypergraph. -/

@[expose] public section
namespace RigidGHZ.Finite

variable {V : Type*} [DecidableEq V] {n e d : ℕ}

theorem exactCover_matching_subset (D : ExactCoverData V n e d) (r : Fin d) :
    D.matching r ⊆ D.host := by
  intro a ha
  obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
  exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩

theorem exactCover_covers_of_indices (D : ExactCoverData V n e d)
    (h : ∀ i, ∃ r, i ∈ D.row r) : D.host = Finset.univ.biUnion D.matching := by
  ext a
  constructor
  · intro ha
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r,hr⟩ := h i
    exact Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,
      Finset.mem_image.mpr ⟨i,List.mem_toFinset.mpr hr,rfl⟩⟩
  · intro ha
    obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp ha
    exact exactCover_matching_subset D r hr

theorem exactCover_perfect_of_indices (D : ExactCoverData V n e d)
    (hinj : Function.Injective D.edge) (r : Fin d)
    (h : ∀ v : V, ((D.row r).toFinset.filter (fun i => v ∈ D.edge i)).card = 1) :
    PerfectMatching D.host (D.matching r) := by
  refine ⟨exactCover_matching_subset D r,fun v => ?_⟩
  rw [ExactCoverData.matching,Finset.filter_image,Finset.card_image_of_injective _ hinj]
  exact h v

theorem exactCover_disjoint_of_indices (D : ExactCoverData V n e d)
    (hinj : Function.Injective D.edge)
    (h : Pairwise (fun r s => Disjoint (D.row r).toFinset (D.row s).toFinset)) :
    Pairwise (fun r s => Disjoint (D.matching r) (D.matching s)) := by
  intro r s hrs
  apply Finset.disjoint_left.mpr
  intro a har has
  obtain ⟨i,hi,hia⟩ := Finset.mem_image.mp har
  obtain ⟨j,hj,hja⟩ := Finset.mem_image.mp has
  have hij := hinj (hia.trans hja.symm)
  subst j
  exact Finset.disjoint_left.mp (h hrs) hi hj

theorem affine_table_injective {m e d : ℕ} [NeZero m]
    (lam : ZMod m) (shift : Fin d → ZMod m) (row : Fin e → Fin d)
    (column : Fin e → ZMod m) (edge : Fin e → Finset (Fin 3 × ZMod m))
    (hshift : Function.Injective shift)
    (hparts : Function.Injective (fun i => (row i,column i)))
    (hedge : ∀ i, edge i = tupleEdge
      (fun j => Supplement.Affine.baseMap lam (shift (row i)) j (column i))) :
    Function.Injective edge := by
  intro i j hij
  rw [hedge i,hedge j] at hij
  have ht := tupleEdge_injective hij
  have hc : column i = column j := congrFun ht 0
  have hs : lam * column i + shift (row i) = lam * column j + shift (row j) := congrFun ht 1
  rw [hc] at hs
  exact hparts (Prod.ext (hshift (add_left_cancel hs)) hc)

theorem affine_host_eq_of_rows {m n e d : ℕ} [NeZero m]
    (D : ExactCoverData (Fin 3 × ZMod m) n e d) (lam : ZMod m)
    (S : Finset (ZMod m)) (shift : Fin d → ZMod m)
    (hmem : ∀ r, shift r ∈ S) (hsurj : ∀ s : S, ∃ r, shift r = s.val)
    (hrow : ∀ r, D.matching r = coordinateMatching (Supplement.Affine.baseMap lam (shift r)))
    (hcover : D.host = Finset.univ.biUnion D.matching) :
    D.host = Supplement.Affine.baseGraph lam S := by
  rw [hcover]
  ext a
  constructor
  · intro ha
    obtain ⟨r,_,hr⟩ := Finset.mem_biUnion.mp ha
    exact Finset.mem_biUnion.mpr ⟨⟨shift r,hmem r⟩,Finset.mem_univ _,by
      simpa only [hrow r] using hr⟩
  · intro ha
    obtain ⟨s,_,hs⟩ := Finset.mem_biUnion.mp ha
    obtain ⟨r,hr⟩ := hsurj s
    refine Finset.mem_biUnion.mpr ⟨r,Finset.mem_univ _,?_⟩
    rw [hrow r,hr]
    exact hs

end RigidGHZ.Finite
