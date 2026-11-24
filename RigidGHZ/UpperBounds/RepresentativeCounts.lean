module

public import RigidGHZ.UpperBounds.ShadowCombinatorics

/-! Completion counts for independent representatives of one perfect matching. -/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {H M : Hypergraph V} {r : ℕ}

/-- Number the vertices of every matching edge by `Fin r`. -/
def matchingCoordinates (hH : Uniform H r) (hM : PerfectMatching H M)
    (e : M) : Fin r ≃ e.1 :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact hH e.1 (hM.subset e.2))).symm

def selectedRepresentative (b : ∀ e : M, Fin r ≃ e.1) (q : M → Fin r) (e : M) : V :=
  (b e (q e)).1

theorem selectedRepresentative_mem (b : ∀ e : M, Fin r ≃ e.1)
    (q : M → Fin r) (e : M) : selectedRepresentative b q e ∈ e.1 := (b e (q e)).2

/-- Possible completing vertices in one matching block, in its local numbering. -/
def blockHits (b : ∀ e : M, Fin r ≃ e.1) (e : M) (a : Fin r) (F : M) :
    Finset (Fin r) :=
  Finset.univ.filter (fun x => insert (b F x).1 (e.1.erase (b e a).1) ∈ H)

def otherHits (b : ∀ e : M, Fin r ≃ e.1) (e : M) (a : Fin r)
    (F : {F : M // F ≠ e}) : Finset (Fin r) := blockHits (H := H) b e a F.1

@[simp] theorem mem_blockHits {b : ∀ e : M, Fin r ≃ e.1}
    {e F : M} {a x : Fin r} :
    x ∈ blockHits (H := H) b e a F ↔ insert (b F x).1 (e.1.erase (b e a).1) ∈ H := by
  simp [blockHits]

/-- The sum of completing vertices over all matching blocks is the shadow codegree. -/
theorem sum_blockHits_eq_codegree (hH : Uniform H r) (hr : 0 < r)
    (hM : PerfectMatching H M) (b : ∀ e : M, Fin r ≃ e.1) (e : M) (a : Fin r) :
    (∑ F : M, (blockHits (H := H) b e a F).card) =
      codegree H (e.1.erase (b e a).1) := by
  classical
  let S := e.1.erase (b e a).1
  have hS : S.card = r - 1 := by
    rw [Finset.card_erase_of_mem (b e a).2, hH e.1 (hM.subset e.2)]
  let T := Finset.univ.sigma (blockHits (H := H) b e a)
  have hbij : T.card = (H.filter (fun K => S ⊆ K)).card := by
    apply Finset.card_bij (fun z _ => insert (b z.1 z.2).1 S)
    · intro z hz
      exact Finset.mem_filter.mpr
        ⟨mem_blockHits.mp (Finset.mem_sigma.mp hz).2, Finset.subset_insert _ _⟩
    · intro z hz t ht heq
      rcases z with ⟨F, x⟩
      rcases t with ⟨G, y⟩
      have hxH : insert (b F x).1 S ∈ H := mem_blockHits.mp (Finset.mem_sigma.mp hz).2
      have hxnot : (b F x).1 ∉ S := completion_not_mem hH hr hS hxH
      have hxy : (b F x).1 = (b G y).1 := (Finset.insert_inj hxnot).mp heq
      have hFG : F = G := matching_edge_eq_of_common hM (b F x).2 (by
        simpa only [hxy] using (b G y).2)
      subst G
      exact congrArg (fun z => Sigma.mk F z) ((b F).injective (Subtype.ext hxy))
    · intro K hK
      obtain ⟨w, hwK, hwS, hw⟩ := exists_completion_vertex
        (Finset.mem_filter.mp hK).2 (by rw [hS, hH K (Finset.mem_filter.mp hK).1]; omega)
      obtain ⟨F, hF, _⟩ := hM.existsUnique_edge w
      let f : M := ⟨F, hF.1⟩
      let x : Fin r := (b f).symm ⟨w, hF.2⟩
      have hcoord : (b f x).1 = w := congrArg Subtype.val ((b f).apply_symm_apply ⟨w, hF.2⟩)
      refine ⟨⟨f, x⟩, ?_, ?_⟩
      · apply Finset.mem_sigma.mpr
        refine ⟨Finset.mem_univ _, mem_blockHits.mpr ?_⟩
        change insert (b f x).1 S ∈ H
        rw [hcoord, hw]
        exact (Finset.mem_filter.mp hK).1
      · change insert (b f x).1 S = K
        rw [hcoord, hw]
  exact (Finset.card_sigma Finset.univ (blockHits (H := H) b e a)).symm.trans hbij

/-- In the original edge, only the original representative completes the shadow set. -/
theorem blockHits_self (hH : Uniform H r) (hr : 0 < r)
    (hM : PerfectMatching H M) (b : ∀ e : M, Fin r ≃ e.1) (e : M) (a : Fin r) :
    blockHits (H := H) b e a e = {a} := by
  classical
  ext x
  simp only [mem_blockHits, Finset.mem_singleton]
  constructor
  · intro hx
    have hS : (e.1.erase (b e a).1).card = r - 1 := by
      rw [Finset.card_erase_of_mem (b e a).2, hH e.1 (hM.subset e.2)]
    have hnot := completion_not_mem hH hr hS hx
    have hcoord : (b e x).1 = (b e a).1 := by
      by_contra hne
      exact hnot (Finset.mem_erase.mpr ⟨hne, (b e x).2⟩)
    exact (b e).injective (Subtype.ext hcoord)
  · intro hxa
    subst x
    rw [Finset.insert_erase (b e a).2]
    exact hM.subset e.2

theorem sum_otherHits_add_one (hH : Uniform H r) (hr : 0 < r)
    (hM : PerfectMatching H M) (b : ∀ e : M, Fin r ≃ e.1) (e : M) (a : Fin r) :
    (∑ F : {F : M // F ≠ e}, (otherHits (H := H) b e a F).card) + 1 =
      codegree H (e.1.erase (b e a).1) := by
  classical
  have hother : (∑ F : {F : M // F ≠ e}, (otherHits (H := H) b e a F).card) =
      ∑ F ∈ Finset.univ.erase e, (blockHits (H := H) b e a F).card := by
    apply Finset.sum_bij (fun F _ => F.1)
    · intro F _
      exact Finset.mem_erase.mpr ⟨F.2, Finset.mem_univ _⟩
    · intro F hF G hG h
      exact Subtype.ext h
    · intro F hF
      exact ⟨⟨F, (Finset.mem_erase.mp hF).1⟩, Finset.mem_univ _, rfl⟩
    · intro F _
      rfl
  have hself : (blockHits (H := H) b e a e).card = 1 := by
    rw [blockHits_self hH hr hM b e a, Finset.card_singleton]
  rw [hother, ← hself, Finset.sum_erase_add _ _ (Finset.mem_univ e)]
  exact sum_blockHits_eq_codegree hH hr hM b e a

/-- The outdegree of a chosen representative is its number of hits in the other blocks. -/
theorem selected_outdegree_eq_hitCount (b : ∀ e : M, Fin r ≃ e.1)
    (q : M → Fin r) (e : M) :
    (Finset.univ.filter (exchangeArc H (selectedRepresentative b q) e)).card =
      (Finset.univ.filter (fun F : {F : M // F ≠ e} =>
        q F.1 ∈ otherHits (H := H) b e (q e) F)).card := by
  classical
  symm
  apply Finset.card_bij (fun F _ => F.1)
  · intro F hF
    have hh := (Finset.mem_filter.mp hF).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, F.2.symm, mem_blockHits.mp hh⟩
  · intro F hF G hG h
    exact Subtype.ext h
  · intro F hF
    have hh := (Finset.mem_filter.mp hF).2
    refine ⟨⟨F, hh.1.symm⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, mem_blockHits.mpr hh.2⟩

end RigidGHZ.UpperBounds
