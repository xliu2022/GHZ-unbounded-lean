module

public import RigidGHZ.Supplement.Periodic.Height

/-! Height certificates yield exhaustive ordinary rigid matching families. -/

@[expose] public section

set_option linter.unusedSectionVars false

namespace RigidGHZ.Supplement.Periodic

variable {E I : Type*} [Fintype E] [DecidableEq E] [DecidableEq I]

 def colorClass (c : E → I) (i : I) : Finset E := Finset.univ.filter (fun e => c e = i)

@[simp] theorem mem_colorClass (c : E → I) (i : I) (e : E) : e ∈ colorClass c i ↔ c e = i := by
  simp [colorClass]

namespace Scheme

variable {V L : Type*} [Fintype V] [Fintype L] [Fintype I]
  [DecidableEq V] [DecidableEq L] (D : Scheme V E)

noncomputable def rigidFamily_of_configurations (σ : Equiv.Perm L) (c : E → I)
    (hlocal : ∀ i, D.LocalConfig (colorClass c i))
    (hloop : ∀ i, D.output (colorClass c i) = D.input (colorClass c i))
    (hcomplete : ∀ A : L → Finset E, D.PeriodicConfig σ A →
      ∃ i, A = fun _ => colorClass c i) : RigidFamily (D.graph σ) I where
  matching := fun i => D.selection σ (fun _ => colorClass c i)
  perfect := fun i => D.periodic_matching σ ⟨fun _ => hlocal i, fun _ => hloop i⟩
  edge_disjoint := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro g hgi hgj
    obtain ⟨k, e, he, heg⟩ := (D.mem_selection σ _ _).mp hgi
    obtain ⟨l, f, hf, hfg⟩ := (D.mem_selection σ _ _).mp hgj
    have hef := D.edge_eq_of_lift_eq σ (heg.trans hfg.symm)
    have hi := (mem_colorClass c i e).mp he
    have hj := (mem_colorClass c j f).mp hf
    exact hij (hi.symm.trans (by simpa only [hef] using hj))
  covers := by
    ext g
    constructor
    · intro hg
      obtain ⟨⟨e, j⟩, he, rfl⟩ := Finset.mem_image.mp hg
      exact Finset.mem_biUnion.mpr ⟨c e, Finset.mem_univ _,
        (D.liftEdge_mem_selection σ _ e j).mpr (by simp)⟩
    · intro hg
      obtain ⟨i, hi, hg⟩ := Finset.mem_biUnion.mp hg
      exact D.selection_subset σ _ hg
  complete := by
    intro M hM
    have hA : D.PeriodicConfig σ (D.take σ M) := D.matching_periodic σ (by
      rw [D.selection_take σ hM.subset]
      exact hM)
    obtain ⟨i, hi⟩ := hcomplete _ hA
    exact ⟨i, by simpa only [hi] using (D.selection_take σ hM.subset).symm⟩

 theorem graph_card (σ : Equiv.Perm L) : (D.graph σ).card = Fintype.card E * Fintype.card L := by
  rw [graph, Finset.card_image_of_injective _ (D.liftEdge_injective σ)]
  simp

variable {q : ℕ}

 theorem constant_of_loop_states (hq : 0 < q) (c : E → I)
    (hinj : Function.Injective (fun i => D.input (colorClass c i)))
    (hloops : ∀ B : Finset E, D.LocalConfig B → D.input B = D.output B →
      ∃ i, B = colorClass c i)
    (A : Fin q → Finset E) (hA : D.PeriodicConfig (finRotate q) A)
    (hstep : ∀ j, D.input (A j) = D.input (A (finRotate q j))) :
    ∃ i, A = fun _ => colorClass c i := by
  classical
  have hc : ∀ j, ∃ i, A j = colorClass c i := by
    intro j
    exact hloops _ (hA.1 j) ((hstep j).trans (hA.2 j).symm)
  choose i hi using hc
  have hiNext : ∀ j, i (finRotate q j) = i j := by
    intro j
    apply hinj
    change D.input (colorClass c (i (finRotate q j))) = D.input (colorClass c (i j))
    rw [← hi (finRotate q j), ← hi j]
    exact (hstep j).symm
  have hic := finRotate_constant hq i hiNext
  refine ⟨i ⟨0, hq⟩, ?_⟩
  funext j
  rw [hi j, hic j ⟨0, hq⟩]

 theorem strict_configurations_complete (hq : 0 < q) (c : E → I)
    (height : Finset V → ℕ)
    (hinj : Function.Injective (fun i => D.input (colorClass c i)))
    (hloops : ∀ B : Finset E, D.LocalConfig B → D.input B = D.output B →
      ∃ i, B = colorClass c i)
    (hheight : ∀ B : Finset E, D.LocalConfig B →
      D.input B = D.output B ∨ height (D.input B) < height (D.output B))
    (A : Fin q → Finset E) (hA : D.PeriodicConfig (finRotate q) A) :
    ∃ i, A = fun _ => colorClass c i := by
  apply D.constant_of_loop_states hq c hinj hloops A hA
  apply strict_height_forces_loops (finRotate q) (fun j => D.input (A j)) height
  intro j
  have h := hheight (A j) (hA.1 j)
  rwa [hA.2 j] at h

 theorem odd_configurations_complete (hq : 0 < q) (hodd : Odd q) (c : E → I)
    (height : Finset V → ℕ) (x y : Finset V) (hxy : x ≠ y)
    (hinj : Function.Injective (fun i => D.input (colorClass c i)))
    (hloops : ∀ B : Finset E, D.LocalConfig B → D.input B = D.output B →
      ∃ i, B = colorClass c i)
    (havoid : ∀ i, D.input (colorClass c i) ≠ x ∧ D.input (colorClass c i) ≠ y)
    (hmono : ∀ B : Finset E, D.LocalConfig B → height (D.input B) ≤ height (D.output B))
    (hflat : ∀ B : Finset E, D.LocalConfig B → height (D.input B) = height (D.output B) →
      D.input B = D.output B ∨ (D.input B = x ∧ D.output B = y) ∨
        (D.input B = y ∧ D.output B = x))
    (A : Fin q → Finset E) (hA : D.PeriodicConfig (finRotate q) A) :
    ∃ i, A = fun _ => colorClass c i := by
  let R : Finset V → Finset V → Prop := fun s t =>
    ∃ B : Finset E, D.LocalConfig B ∧ D.input B = s ∧ D.output B = t
  have hRmono : ∀ s t, R s t → height s ≤ height t := by
    rintro s t ⟨B, hB, rfl, rfl⟩
    exact hmono B hB
  have hRflat : ∀ s t, R s t → height s = height t →
      s = t ∨ (s = x ∧ t = y) ∨ (s = y ∧ t = x) := by
    rintro s t ⟨B, hB, rfl, rfl⟩ he
    exact hflat B hB he
  have hnx : ¬R x x := by
    rintro ⟨B, hB, hin, hout⟩
    obtain ⟨i, hi⟩ := hloops B hB (hin.trans hout.symm)
    exact (havoid i).1 (by simpa only [hi] using hin)
  have hny : ¬R y y := by
    rintro ⟨B, hB, hin, hout⟩
    obtain ⟨i, hi⟩ := hloops B hB (hin.trans hout.symm)
    exact (havoid i).2 (by simpa only [hi] using hin)
  apply D.constant_of_loop_states hq c hinj hloops A hA
  apply odd_height_forces_loops hq hodd R height x y hxy hRmono hRflat hnx hny
  intro j
  exact ⟨A j, hA.1 j, rfl, hA.2 j⟩

end Scheme
end RigidGHZ.Supplement.Periodic
