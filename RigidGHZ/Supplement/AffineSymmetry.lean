module

public import RigidGHZ.Supplement.AffineSeed
public import RigidGHZ.Relabel

/-! Translation symmetry used to normalize ordinary affine-seed counterexamples
before checking their finite exact-cover certificates. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.Supplement.Affine

open scoped BigOperators

variable {m : ℕ} [NeZero m]

/-- Simultaneous affine translation of the three vertex parts. -/
def translate (lam t : ZMod m) : Equiv.Perm (Fin 3 × ZMod m) :=
  Equiv.prodCongrRight ![Equiv.addRight t, Equiv.addRight (lam * t),
    Equiv.addRight (-(lam + 1) * t)]

 theorem relabel_tuple_parts {W : Type*} [DecidableEq W]
    (p : Fin 3 → Equiv.Perm W) (x : Fin 3 → W) :
    relabelEdge (Equiv.prodCongrRight p) (tupleEdge x) = tupleEdge (fun j => p j (x j)) := by
  ext ⟨j, w⟩
  simp only [mem_relabelEdge, Equiv.prodCongrRight_symm, Equiv.prodCongrRight_apply,
    Function.comp_apply, mem_tupleEdge]
  exact Equiv.symm_apply_eq (p j)

 theorem translate_edge (lam t s a : ZMod m) :
    relabelEdge (translate lam t) (tupleEdge (fun j => baseMap lam s j a)) =
      tupleEdge (fun j => baseMap lam s j (a + t)) := by
  rw [translate, relabel_tuple_parts]
  congr 1
  funext j
  fin_cases j <;> simp [baseMap] <;> ring

 theorem translate_matching (lam t s : ZMod m) :
    relabelHypergraph (translate lam t) (coordinateMatching (baseMap lam s)) =
      coordinateMatching (baseMap lam s) := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hf
    rw [translate_edge]
    exact Finset.mem_image.mpr ⟨a + t, Finset.mem_univ _, rfl⟩
  · intro he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    refine Finset.mem_image.mpr ⟨tupleEdge (fun j => baseMap lam s j (a - t)),
      Finset.mem_image.mpr ⟨a - t, Finset.mem_univ _, rfl⟩, ?_⟩
    rw [translate_edge, sub_add_cancel]

 theorem translate_graph (lam t : ZMod m) (S : Finset (ZMod m)) :
    relabelHypergraph (translate lam t) (baseGraph lam S) = baseGraph lam S := by
  ext e
  constructor
  · intro he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    obtain ⟨s, hs, hfs⟩ := Finset.mem_biUnion.mp hf
    apply Finset.mem_biUnion.mpr
    refine ⟨s, Finset.mem_univ _, ?_⟩
    rw [← translate_matching lam t s.val]
    exact Finset.mem_image.mpr ⟨f, hfs, rfl⟩
  · intro he
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp he
    rw [← translate_matching lam t s.val] at hes
    obtain ⟨f, hfs, hfe⟩ := Finset.mem_image.mp hes
    exact Finset.mem_image.mpr ⟨f, Finset.mem_biUnion.mpr ⟨s, Finset.mem_univ _, hfs⟩, hfe⟩

 theorem translate_matching_injective (lam t : ZMod m) :
    Function.Injective (relabelHypergraph (translate lam t)) := by
  intro H K h
  have hh := congrArg (relabelHypergraph (translate lam t).symm) h
  simpa only [relabelHypergraph_symm] using hh

/-- Any non-prescribed ordinary perfect matching has a translated representative
whose least present shift contains its row at first coordinate zero. Every
smaller shift is absent. These are exactly the fixed-edge SAT branches. -/
 theorem normalize_counterexample (lam : ZMod m) (S : Finset (ZMod m))
    {M : Hypergraph (Fin 3 × ZMod m)} (hM : PerfectMatching (baseGraph lam S) M)
    (hne : ∀ s : S, M ≠ coordinateMatching (baseMap lam s.val)) :
    ∃ M' : Hypergraph (Fin 3 × ZMod m), ∃ s : S,
      PerfectMatching (baseGraph lam S) M' ∧
      (∀ t : S, M' ≠ coordinateMatching (baseMap lam t.val)) ∧
      tupleEdge (fun j => baseMap lam s.val j 0) ∈ M' ∧
      ∀ t : S, t.val.val < s.val.val → ∀ a,
        tupleEdge (fun j => baseMap lam t.val j a) ∉ M' := by
  classical
  let T := Finset.univ.filter (fun s : S => ∃ a, tupleEdge (fun j => baseMap lam s.val j a) ∈ M)
  have hT : T.Nonempty := by
    obtain ⟨e, he⟩ := hM.nonempty
    obtain ⟨s, hs, hes⟩ := Finset.mem_biUnion.mp (hM.subset he)
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hes
    exact ⟨s, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨a, he⟩⟩⟩
  obtain ⟨s, hs, hmin⟩ := T.exists_min_image (fun s => s.val.val) hT
  obtain ⟨a, ha⟩ := (Finset.mem_filter.mp hs).2
  let M' := relabelHypergraph (translate lam (-a)) M
  refine ⟨M', s, ?_, ?_, ?_, ?_⟩
  · have hh := hM.relabel (translate lam (-a))
    simpa only [translate_graph] using hh
  · intro t ht
    apply hne t
    apply translate_matching_injective lam (-a)
    exact ht.trans (translate_matching lam (-a) t.val).symm
  · have hh : relabelEdge (translate lam (-a)) (tupleEdge (fun j => baseMap lam s.val j a)) ∈ M' :=
      Finset.mem_image.mpr ⟨_, ha, rfl⟩
    simpa only [translate_edge, add_neg_cancel] using hh
  · intro t ht b hb
    have hold : tupleEdge (fun j => baseMap lam t.val j (b + a)) ∈ M := by
      apply (relabelEdge_mem_relabelHypergraph (translate lam (-a)) _ M).mp
      rw [translate_edge]
      simpa only [add_neg_cancel_right] using hb
    have htT : t ∈ T := Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨b + a, hold⟩⟩
    exact (not_lt_of_ge (hmin t htT)) ht

end RigidGHZ.Supplement.Affine
