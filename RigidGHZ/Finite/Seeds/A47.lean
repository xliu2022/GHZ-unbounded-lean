module

public import RigidGHZ.Finite.Seeds.A47Case0
public import RigidGHZ.Finite.Seeds.A47Case1
public import RigidGHZ.Finite.Seeds.A47Case2
public import RigidGHZ.Finite.Seeds.A47Case3
public import RigidGHZ.Finite.Seeds.A47Case4
public import RigidGHZ.Supplement.AffineSymmetry

/-! Translation normalization plus the independently checked finite branches
proves completeness for the ordinary affine hypergraph. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47
open RigidGHZ.Supplement.Affine
set_option maxRecDepth 1000000
set_option maxHeartbeats 0

theorem complete : ∀ M, PerfectMatching data.host M → ∃ r, M = data.matching r := by
  intro M hM
  by_contra hn
  push_neg at hn
  have hne : ∀ s : shifts, M ≠ coordinateMatching (baseMap (1 : ZMod 47) s.val) := by
    intro s hs
    obtain ⟨r,hr⟩ := shift_surjective s
    apply hn r
    rw [matching_eq r,hr]
    exact hs
  obtain ⟨M',s,hM',hne',hroot,hlower⟩ := normalize_counterexample
    (1 : ZMod 47) shifts (by simpa only [host_eq] using hM) hne
  obtain ⟨r,hr⟩ := shift_surjective s
  have hPM : PerfectMatching data.host M' := by simpa only [host_eq] using hM'
  have hnot : ∀ t, M' ≠ data.matching t := by
    intro t ht
    exact hne' ⟨shift t,shift_mem t⟩ (ht.trans (matching_eq t))
  have hroot' : data.edge (rootIndex r) ∈ M' := by
    rw [root_edge_eq r,hr]
    exact hroot
  have hlower' : ∀ i : Fin 235, i.val < r.val * 47 → data.edge i ∉ M' := by
    intro i hi
    rw [edge_eq i]
    apply hlower ⟨shift (rowIndex i),shift_mem (rowIndex i)⟩
    rw [← hr]
    exact lower_shift r i hi
  fin_cases r
  · exact Case0.refutation M' hPM hnot hroot' hlower'
  · exact Case1.refutation M' hPM hnot hroot' hlower'
  · exact Case2.refutation M' hPM hnot hroot' hlower'
  · exact Case3.refutation M' hPM hnot hroot' hlower'
  · exact Case4.refutation M' hPM hnot hroot' hlower'

noncomputable def family : RigidFamily data.host (Fin 5) := valid.family complete
theorem rigid : IsRigid data.host 5 := ⟨family⟩

end RigidGHZ.Finite.Seeds.A47
