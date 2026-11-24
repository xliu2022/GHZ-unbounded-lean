module

public import RigidGHZ.Supplement.AffineSeed
public import RigidGHZ.Finite.Seeds.A3
public import RigidGHZ.Finite.Seeds.A3Facts
public import RigidGHZ.Finite.Seeds.A5
public import RigidGHZ.Finite.Seeds.A5Facts
public import RigidGHZ.Finite.Seeds.A7
public import RigidGHZ.Finite.Seeds.A7Facts

/-! Kernel-checked ordinary affine seeds at part sizes 3, 5, and 7. -/

@[expose] public section

namespace RigidGHZ.Supplement.Affine


/-- Convert a finite row-choice check into the paper's ordinary seed hypothesis. -/
theorem seed_of_row_certificate {m : ℕ} [NeZero m]
    (lam : ZMod m) (S : Finset (ZMod m))
    (hlam : IsUnit lam) (hlam1 : IsUnit (lam + 1))
    (hcert : ∀ c : ZMod m → S,
      (∀ j, Function.Injective (fun a => baseMap lam (c a).val j a)) →
      ∃ s : S, ∀ a j, baseMap lam (c a).val j a = baseMap lam s.val j a) : Seed lam S := by
  refine ⟨hlam, hlam1, ?_⟩
  intro M hM
  have htrans : ∀ e ∈ baseGraph lam S, ∃ x : Fin 3 → ZMod m, e = tupleEdge x := by
    intro e he
    obtain ⟨s, hs, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    exact ⟨fun j => baseMap lam s.val j a, rfl⟩
  obtain ⟨q, hq0, hMq⟩ := perfectMatching_coordinates 0 htrans hM
  have hrow : ∀ a, ∃ s : S, ∀ j, q j a = baseMap lam s.val j a := by
    intro a
    have he : tupleEdge (fun j => q j a) ∈ baseGraph lam S := by
      apply hM.subset
      rw [hMq]
      exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    obtain ⟨s, hs, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨b, hb, he⟩ := Finset.mem_image.mp he
    have hv := tupleEdge_injective he
    have hba : b = a := by
      have h := congrFun hv 0
      simpa [baseMap, hq0] using h
    subst b
    exact ⟨s, fun j => (congrFun hv j).symm⟩
  choose c hc using hrow
  have hi : ∀ j, Function.Injective (fun a => baseMap lam (c a).val j a) := by
    intro j a b he
    apply (q j).injective
    rw [hc a j, hc b j]
    exact he
  obtain ⟨s, hs⟩ := hcert c hi
  refine ⟨s, hMq.trans ?_⟩
  unfold coordinateMatching
  congr 1
  funext a
  congr 1
  funext j
  exact (hc a j).trans (hs a j)

def shifts3 : Finset (ZMod 3) := {0, 1, 2}
def shifts5 : Finset (ZMod 5) := {0, 1, 2, 3}
def shifts7 : Finset (ZMod 7) := {0, 1, 2, 3}

theorem seed3 : Seed (1 : ZMod 3) shifts3 := by
  refine ⟨isUnit_one, ?_, ?_⟩
  · change IsUnit (2 : ZMod 3)
    exact (ZMod.isUnit_iff_coprime 2 3).mpr (by decide)
  · intro M hM
    have hM' : PerfectMatching Finite.Seeds.A3.data.host M := by
      rw [Finite.Seeds.A3.host_eq]
      exact hM
    obtain ⟨r, hr⟩ := Finite.Seeds.A3.complete M hM'
    refine ⟨⟨Finite.Seeds.A3.shift r, Finite.Seeds.A3.shift_mem r⟩, ?_⟩
    exact hr.trans (Finite.Seeds.A3.matching_eq r)

theorem seed5 : Seed (1 : ZMod 5) shifts5 := by
  refine ⟨isUnit_one, ?_, ?_⟩
  · change IsUnit (2 : ZMod 5)
    exact (ZMod.isUnit_iff_coprime 2 5).mpr (by decide)
  · intro M hM
    have hM' : PerfectMatching Finite.Seeds.A5.data.host M := by
      rw [Finite.Seeds.A5.host_eq]
      exact hM
    obtain ⟨r, hr⟩ := Finite.Seeds.A5.complete M hM'
    refine ⟨⟨Finite.Seeds.A5.shift r, Finite.Seeds.A5.shift_mem r⟩, ?_⟩
    exact hr.trans (Finite.Seeds.A5.matching_eq r)

theorem seed7 : Seed (1 : ZMod 7) shifts7 := by
  refine ⟨isUnit_one, ?_, ?_⟩
  · change IsUnit (2 : ZMod 7)
    exact (ZMod.isUnit_iff_coprime 2 7).mpr (by decide)
  · intro M hM
    have hM' : PerfectMatching Finite.Seeds.A7.data.host M := by
      rw [Finite.Seeds.A7.host_eq]
      exact hM
    obtain ⟨r, hr⟩ := Finite.Seeds.A7.complete M hM'
    refine ⟨⟨Finite.Seeds.A7.shift r, Finite.Seeds.A7.shift_mem r⟩, ?_⟩
    exact hr.trans (Finite.Seeds.A7.matching_eq r)

theorem shifts3_card : shifts3.card = 3 := by decide +kernel
theorem shifts5_card : shifts5.card = 4 := by decide +kernel
theorem shifts7_card : shifts7.card = 4 := by decide +kernel

end RigidGHZ.Supplement.Affine
