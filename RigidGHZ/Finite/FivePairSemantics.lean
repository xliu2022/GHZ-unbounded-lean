module

public import RigidGHZ.Finite.FivePairData

/-! Recovering a color-indexed family from arbitrary selected vertices in the
ordinary bipartite graph, and interpreting the finite certificates. -/

@[expose] public section

namespace RigidGHZ.Finite.FivePair

variable {I : Type*} [Fintype I] [DecidableEq I]
  {L R : Finset Pair} {c : I → Fin 5} {f : I → Fin 6}

theorem family_crossFree (h : Conditions L R) (hc : Function.Injective c)
    (hL : ∀ i, choice (c i) (f i) ∈ L) (hR : ∀ i, partner (c i) (f i) ∈ R) :
    CrossFree c f := by
  intro i j hij hadj
  have hp := h.right_unique _ (hR j) _ (hL i) _ (hL j) hadj (choice_adj _ _)
  have hq := h.left_unique _ (hL i) _ (hR i) _ (hR j) (choice_adj _ _) hadj
  apply hij
  apply hc
  calc
    c i = color (choice (c i) (f i)) (partner (c i) (f i)) := (choice_color _ _).symm
    _ = color (choice (c j) (f j)) (partner (c j) (f j)) := congrArg₂ color hp hq
    _ = c j := choice_color _ _

theorem family_left_injective (h : CrossFree c f) :
    Function.Injective (fun i => choice (c i) (f i)) := by
  intro i j hij
  change choice (c i) (f i) = choice (c j) (f j) at hij
  by_contra hne
  apply h i j hne
  rw [hij]
  exact choice_adj _ _

theorem family_right_injective (h : CrossFree c f) :
    Function.Injective (fun i => partner (c i) (f i)) := by
  intro i j hij
  change partner (c i) (f i) = partner (c j) (f j) at hij
  by_contra hne
  apply h i j hne
  rw [← hij]
  exact choice_adj _ _

theorem leftFamily_card (h : CrossFree c f) : (leftFamily c f).card = Fintype.card I := by
  rw [leftFamily, Finset.card_image_of_injective _ (family_left_injective h), Finset.card_univ]

theorem rightFamily_card (h : CrossFree c f) : (rightFamily c f).card = Fintype.card I := by
  rw [rightFamily, Finset.card_image_of_injective _ (family_right_injective h), Finset.card_univ]

theorem edgeFamily_card (h : CrossFree c f) : (edgeFamily c f).card = Fintype.card I := by
  have hinj : Function.Injective (fun i => (choice (c i) (f i), partner (c i) (f i))) := by
    intro i j hij
    exact family_left_injective h (congrArg Prod.fst hij)
  rw [edgeFamily, Finset.card_image_of_injective _ hinj, Finset.card_univ]

theorem leftFamily_subset (hL : ∀ i, choice (c i) (f i) ∈ L) : leftFamily c f ⊆ L := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact hL i

theorem rightFamily_subset (hR : ∀ i, partner (c i) (f i) ∈ R) : rightFamily c f ⊆ R := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact hR i

theorem family_edges_eq (hcross : CrossFree c f)
    (hL : ∀ i, choice (c i) (f i) ∈ L) (hR : ∀ i, partner (c i) (f i) ∈ R)
    (hcount : (edges L R).card = Fintype.card I) : edges L R = edgeFamily c f := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro e he
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    exact mem_edges.mpr ⟨hL i, hR i, choice_adj _ _⟩
  · rw [hcount, edgeFamily_card hcross]

theorem left_difference_subset (h : Conditions L R)
    (hL : ∀ i, choice (c i) (f i) ∈ L) (hR : ∀ i, partner (c i) (f i) ∈ R) :
    L \ leftFamily c f ⊆ extraLeft c f := by
  intro p hp
  obtain ⟨hpL, hpnot⟩ := Finset.mem_sdiff.mp hp
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hadj
  have heq := h.right_unique _ (hR i) _ hpL _ (hL i) hadj (choice_adj _ _)
  exact hpnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩)

theorem right_difference_subset (h : Conditions L R)
    (hL : ∀ i, choice (c i) (f i) ∈ L) (hR : ∀ i, partner (c i) (f i) ∈ R) :
    R \ rightFamily c f ⊆ extraRight c f := by
  intro q hq
  obtain ⟨hqR, hqnot⟩ := Finset.mem_sdiff.mp hq
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  intro i hadj
  have heq := h.left_unique _ (hL i) _ hqR _ (hR i) hadj (choice_adj _ _)
  exact hqnot (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, heq.symm⟩)

theorem color_image_card (h : Conditions L R) :
    ((edges L R).image (fun e => color e.1 e.2)).card = (edges L R).card := by
  apply Finset.card_image_of_injOn
  intro e he g hg hcol
  exact h.color_unique e he g hg hcol

theorem choice_of_color_mem {c : Fin 5} (hcol : c ∈ (edges L R).image (fun e => color e.1 e.2)) :
    ∃ j : Fin 6, choice c j ∈ L ∧ partner c j ∈ R := by
  obtain ⟨⟨p, q⟩, hpq, hc⟩ := Finset.mem_image.mp hcol
  obtain ⟨hp, hq, hadj⟩ := mem_edges.mp hpq
  obtain ⟨j, rfl, rfl⟩ := choice_complete c p q hadj hc
  exact ⟨j, hp, hq⟩

/-- Five distinct edge colors exhaust the ground set. -/
theorem extract_five (h : Conditions L R) (hcount : (edges L R).card = 5) :
    ∃ f : Fin 5 → Fin 6, (∀ i, choice i (f i) ∈ L) ∧ (∀ i, partner i (f i) ∈ R) := by
  classical
  have hcs : (edges L R).image (fun e => color e.1 e.2) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [color_image_card h, hcount, Finset.card_univ, Fintype.card_fin]
  have hf : ∀ i : Fin 5, ∃ j : Fin 6, choice i j ∈ L ∧ partner i j ∈ R := by
    intro i
    apply choice_of_color_mem
    rw [hcs]
    exact Finset.mem_univ _
  choose f hf using hf
  exact ⟨f, fun i => (hf i).1, fun i => (hf i).2⟩

/-- Four distinct colors omit one point. The remaining colors are indexed by
`Fin.succAbove`, without any symmetry assumption on the selected sets. -/
theorem extract_four (h : Conditions L R) (hcount : (edges L R).card = 4) :
    ∃ c : Fin 5, ∃ f : Fin 4 → Fin 6,
      (∀ i, choice (c.succAbove i) (f i) ∈ L) ∧
      (∀ i, partner (c.succAbove i) (f i) ∈ R) := by
  classical
  let cs := (edges L R).image (fun e => color e.1 e.2)
  have hcs : cs.card = 4 := (color_image_card h).trans hcount
  have hcomp : (Finset.univ \ cs).card = 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      Fintype.card_fin, hcs]
  obtain ⟨c, hc⟩ := Finset.card_eq_one.mp hcomp
  have hmem : ∀ i : Fin 4, c.succAbove i ∈ cs := by
    intro i
    by_contra hi
    have hin : c.succAbove i ∈ Finset.univ \ cs :=
      Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hi⟩
    rw [hc] at hin
    exact Fin.succAbove_ne c i (Finset.mem_singleton.mp hin)
  have hf : ∀ i : Fin 4, ∃ j : Fin 6,
      choice (c.succAbove i) j ∈ L ∧ partner (c.succAbove i) j ∈ R := by
    intro i
    exact choice_of_color_mem (hmem i)
  choose f hf using hf
  exact ⟨c, f, fun i => (hf i).1, fun i => (hf i).2⟩

theorem five_conclusion (h : Conditions L R) {f : Fin 5 → Fin 6}
    (hL : ∀ i, choice i (f i) ∈ L) (hR : ∀ i, partner i (f i) ∈ R)
    (hleft : extraLeft id f = ∅) (hright : extraRight id f = ∅) :
    L.card + R.card = 10 := by
  have hcross : CrossFree id f := family_crossFree h Function.injective_id hL hR
  have hlc : (leftFamily id f).card = 5 := leftFamily_card hcross
  have hrc : (rightFamily id f).card = 5 := rightFamily_card hcross
  have hls := leftFamily_subset (c := id) hL
  have hrs := rightFamily_subset (c := id) hR
  have hld := Finset.card_le_card (left_difference_subset (c := id) h hL hR)
  have hrd := Finset.card_le_card (right_difference_subset (c := id) h hL hR)
  rw [hleft, Finset.card_empty, Finset.card_sdiff_of_subset hls, hlc] at hld
  rw [hright, Finset.card_empty, Finset.card_sdiff_of_subset hrs, hrc] at hrd
  have hle := Finset.card_le_card hls
  have hre := Finset.card_le_card hrs
  rw [hlc] at hle
  rw [hrc] at hre
  omega

theorem four_conclusion (h : Conditions L R) {c : Fin 5} {f : Fin 4 → Fin 6}
    (hcount : (edges L R).card = 4)
    (hL : ∀ i, choice (c.succAbove i) (f i) ∈ L)
    (hR : ∀ i, partner (c.succAbove i) (f i) ∈ R)
    (hleft : (extraLeft c.succAbove f).card ≤ 1)
    (hright : (extraRight c.succAbove f).card ≤ 1)
    (hadj : ∀ p ∈ extraLeft c.succAbove f, ∀ q ∈ extraRight c.succAbove f, Adj p q) :
    L.card + R.card ≤ 9 := by
  have hcross : CrossFree c.succAbove f :=
    family_crossFree h (Fin.succAbove_right_injective (p := c)) hL hR
  have hlc : (leftFamily c.succAbove f).card = 4 := leftFamily_card hcross
  have hrc : (rightFamily c.succAbove f).card = 4 := rightFamily_card hcross
  have hls := leftFamily_subset hL
  have hrs := rightFamily_subset hR
  have hld := left_difference_subset h hL hR
  have hrd := right_difference_subset h hL hR
  have hldc := (Finset.card_le_card hld).trans hleft
  have hrdc := (Finset.card_le_card hrd).trans hright
  have hnot : ¬((L \ leftFamily c.succAbove f).Nonempty ∧
      (R \ rightFamily c.succAbove f).Nonempty) := by
    rintro ⟨⟨p, hp⟩, ⟨q, hq⟩⟩
    have he : (p, q) ∈ edges L R := mem_edges.mpr
      ⟨(Finset.mem_sdiff.mp hp).1, (Finset.mem_sdiff.mp hq).1, hadj p (hld hp) q (hrd hq)⟩
    rw [family_edges_eq hcross hL hR hcount] at he
    obtain ⟨i, hi, heq⟩ := Finset.mem_image.mp he
    exact (Finset.mem_sdiff.mp hp).2
      (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, congrArg Prod.fst heq⟩)
  rw [← Finset.card_pos, ← Finset.card_pos] at hnot
  rw [Finset.card_sdiff_of_subset hls, hlc] at hldc hnot
  rw [Finset.card_sdiff_of_subset hrs, hrc] at hrdc hnot
  have hle := Finset.card_le_card hls
  have hre := Finset.card_le_card hrs
  rw [hlc] at hle
  rw [hrc] at hre
  omega

end RigidGHZ.Finite.FivePair
