module

public import RigidGHZ.Partite

/-!
# Relabeling and canonical balanced vertex sets

These equivalences identify the usual arbitrary finite vertex sets with the
coordinate vertex sets used by the construction and finite extremal theorems.
-/

@[expose] public section

namespace RigidGHZ

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Transport an edge along a vertex equivalence. -/
def relabelEdge (f : V ≃ W) (e : Finset V) : Finset W := e.map f.toEmbedding

/-- Transport a simple finite hypergraph along a vertex equivalence. -/
def relabelHypergraph (f : V ≃ W) (H : Hypergraph V) : Hypergraph W :=
  H.image (relabelEdge f)

 theorem relabelEdge_injective (f : V ≃ W) : Function.Injective (relabelEdge f) :=
  Finset.map_injective f.toEmbedding

@[simp] theorem mem_relabelEdge (f : V ≃ W) (e : Finset V) (w : W) :
    w ∈ relabelEdge f e ↔ f.symm w ∈ e := by
  constructor
  · intro h
    obtain ⟨v, hv, hfv⟩ := Finset.mem_map.mp h
    simpa only [← hfv, Equiv.toEmbedding_apply, Equiv.symm_apply_apply] using hv
  · intro h
    exact Finset.mem_map.mpr ⟨f.symm w, h, f.apply_symm_apply w⟩

@[simp] theorem relabelEdge_card (f : V ≃ W) (e : Finset V) :
    (relabelEdge f e).card = e.card := Finset.card_map _

@[simp] theorem relabelEdge_symm (f : V ≃ W) (e : Finset V) :
    relabelEdge f.symm (relabelEdge f e) = e := by
  ext v
  simp

@[simp] theorem relabelEdge_apply_symm (f : V ≃ W) (e : Finset W) :
    relabelEdge f (relabelEdge f.symm e) = e := relabelEdge_symm f.symm e

@[simp] theorem relabelHypergraph_symm (f : V ≃ W) (H : Hypergraph V) :
    relabelHypergraph f.symm (relabelHypergraph f H) = H := by
  simp [relabelHypergraph, Finset.image_image, Function.comp_def]

@[simp] theorem relabelHypergraph_apply_symm (f : V ≃ W) (H : Hypergraph W) :
    relabelHypergraph f (relabelHypergraph f.symm H) = H := relabelHypergraph_symm f.symm H

@[simp] theorem relabelEdge_mem_relabelHypergraph (f : V ≃ W)
    (e : Finset V) (H : Hypergraph V) :
    relabelEdge f e ∈ relabelHypergraph f H ↔ e ∈ H := by
  exact Finset.mem_image.trans ⟨by
    rintro ⟨x, hx, he⟩
    rwa [relabelEdge_injective f he] at hx,
    fun h => ⟨e, h, rfl⟩⟩

 theorem Uniform.relabel {H : Hypergraph V} {r : ℕ} (h : Uniform H r) (f : V ≃ W) :
    Uniform (relabelHypergraph f H) r := by
  intro e he
  obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
  simpa using h x hx

 theorem PerfectMatching.relabel {H M : Hypergraph V} (h : PerfectMatching H M)
    (f : V ≃ W) : PerfectMatching (relabelHypergraph f H) (relabelHypergraph f M) := by
  apply PerfectMatching.of_existsUnique
  · intro e he
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he
    exact Finset.mem_image.mpr ⟨x, h.subset hx, rfl⟩
  · intro w
    obtain ⟨e, he, hu⟩ := h.existsUnique_edge (f.symm w)
    refine ⟨relabelEdge f e, ?_, ?_⟩
    · exact ⟨(relabelEdge_mem_relabelHypergraph f e M).mpr he.1,
        (mem_relabelEdge f e w).mpr he.2⟩
    · intro e' he'
      obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp he'.1
      have hxe : x = e := hu x ⟨hx, (mem_relabelEdge f x w).mp he'.2⟩
      rw [hxe]

/-- Transport the complete rigid matching decomposition along a vertex equivalence. -/
def RigidFamily.relabel {H : Hypergraph V} {I : Type*} [Fintype I]
    (R : RigidFamily H I) (f : V ≃ W) : RigidFamily (relabelHypergraph f H) I where
  matching := fun i => relabelHypergraph f (R.matching i)
  perfect := fun i => (R.perfect i).relabel f
  edge_disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro e hei hej
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp hei
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp hej
    have hxy : x = y := relabelEdge_injective f (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp (R.edge_disjoint hij) hx (by simpa only [hxy] using hy)
  covers := by
    ext e
    simp only [relabelHypergraph, Finset.mem_image, Finset.mem_biUnion,
      Finset.mem_univ, true_and]
    constructor
    · rintro ⟨x, hx, hxe⟩
      obtain ⟨i, hxi⟩ := R.mem_iff.mp hx
      exact ⟨i, x, hxi, hxe⟩
    · rintro ⟨i, x, hxi, hxe⟩
      exact ⟨x, R.mem_iff.mpr ⟨i, hxi⟩, hxe⟩
  complete := by
    intro M hM
    have hback : PerfectMatching H (relabelHypergraph f.symm M) := by
      simpa using hM.relabel f.symm
    obtain ⟨i, hi⟩ := R.complete _ hback
    refine ⟨i, ?_⟩
    have hh := congrArg (relabelHypergraph f) hi
    simpa using hh

 theorem IsRigid.relabel {H : Hypergraph V} {d : ℕ} (h : IsRigid H d) (f : V ≃ W) :
    IsRigid (relabelHypergraph f H) d := by
  obtain ⟨R⟩ := h
  exact ⟨R.relabel f⟩

/-- A balanced multipartite hypergraph on an arbitrary finite vertex set has a
canonical coordinate realization, preserving the ordinary edge sets by an equivalence. -/
theorem BalancedPartite.canonical [Fintype V] {H : Hypergraph V} {r m : ℕ}
    (h : BalancedPartite H r m) :
    ∃ f : V ≃ (Fin r × Fin m),
      ∀ e ∈ relabelHypergraph f H, ∃ x : Fin r → Fin m, e = tupleEdge x := by
  classical
  obtain ⟨color, hparts, hedges⟩ := h
  have hcard : ∀ i : Fin r, Fintype.card {v : V // color v = i} = m := by
    intro i
    rw [Fintype.card_subtype]
    exact hparts i
  let eqv : ∀ i : Fin r, {v : V // color v = i} ≃ Fin m := fun i =>
    (Fintype.equivFin _).trans (finCongr (hcard i))
  let f : V ≃ (Fin r × Fin m) := (Equiv.sigmaFiberEquiv color).symm.trans
    (Equiv.sigmaEquivProdOfEquiv eqv)
  have hfcolor : ∀ v : V, (f v).1 = color v := by intro v; rfl
  refine ⟨f, ?_⟩
  intro e he
  obtain ⟨e0, he0, rfl⟩ := Finset.mem_image.mp he
  have hone : ∀ i : Fin r, ∃ v : V, e0.filter (fun v => color v = i) = {v} := by
    intro i
    exact Finset.card_eq_one.mp (hedges e0 he0 i)
  choose v hv using hone
  have hvmem : ∀ i, v i ∈ e0 ∧ color (v i) = i := by
    intro i
    have hh : v i ∈ e0.filter (fun w => color w = i) := by rw [hv i]; simp
    exact Finset.mem_filter.mp hh
  refine ⟨fun i => (f (v i)).2, ?_⟩
  ext z
  rcases z with ⟨i, j⟩
  constructor
  · intro hz
    obtain ⟨w, hw, hfw⟩ := Finset.mem_map.mp hz
    have hwcolor : color w = i := (hfcolor w).symm.trans (congrArg Prod.fst hfw)
    have hwi : w = v i := by
      have hh : w ∈ e0.filter (fun w => color w = i) := Finset.mem_filter.mpr ⟨hw, hwcolor⟩
      rw [hv i] at hh
      exact Finset.mem_singleton.mp hh
    apply mem_tupleEdge.mpr
    change j = (f (v i)).2
    rw [← hwi]
    exact (congrArg Prod.snd hfw).symm
  · intro hz
    have hj : j = (f (v i)).2 := (mem_tupleEdge (x := fun k => (f (v k)).2)).mp hz
    apply Finset.mem_map.mpr
    refine ⟨v i, (hvmem i).1, ?_⟩
    apply Prod.ext
    · exact (hfcolor (v i)).trans (hvmem i).2
    · exact hj.symm

/-- Rigidity is retained when a balanced multipartite hypergraph is put on the
canonical product vertex set. -/
theorem IsRigid.canonical [Fintype V] {H : Hypergraph V} {r m d : ℕ}
    (hR : IsRigid H d) (hP : BalancedPartite H r m) :
    ∃ K : Hypergraph (Fin r × Fin m), IsRigid K d ∧
      (∀ e ∈ K, ∃ x : Fin r → Fin m, e = tupleEdge x) := by
  obtain ⟨f, hf⟩ := hP.canonical
  exact ⟨relabelHypergraph f H, hR.relabel f, hf⟩

end RigidGHZ
