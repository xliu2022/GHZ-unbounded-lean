module

public import RigidGHZ.UpperBounds.Exchange
public import Mathlib.GroupTheory.Perm.Finite
public import Mathlib.Data.Finset.Max
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

/-!
# The reciprocal outdegree bound

A loopless finite digraph with no proper supported permutation is either
sink-free with every outdegree equal to one, or every nonempty induced subgraph
has a sink. The latter case gives the harmonic bound by removing sinks.
-/

@[expose] public section

noncomputable section

namespace RigidGHZ.UpperBounds

open scoped BigOperators

variable {W : Type*} [DecidableEq W] [Fintype W]

/-- A sink-free nonempty finite induced subgraph contains a nontrivial
permutation supported on its arcs, extended by the identity outside the set. -/
theorem sinkfree_supported_permutation (R : W → W → Prop)
    (hirr : ∀ w, ¬ R w w) (S : Finset W) (hS : S.Nonempty)
    (hout : ∀ w ∈ S, ∃ u ∈ S, R w u) :
    ∃ q : Equiv.Perm W,
      (∀ w, q w = w ∨ R w (q w)) ∧ q ≠ Equiv.refl W ∧
        ∀ w ∉ S, q w = w := by
  classical
  let f : W → W := fun w => if hw : w ∈ S then Classical.choose (hout w hw) else w
  have hf : ∀ w ∈ S, f w ∈ S ∧ R w (f w) := by
    intro w hw
    simpa only [f, dif_pos hw] using Classical.choose_spec (hout w hw)
  let C : Finset (Finset W) := S.powerset.filter
    (fun T => T.Nonempty ∧ ∀ w ∈ T, f w ∈ T)
  have hCS : S ∈ C := by
    simp only [C, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨Finset.Subset.refl _, hS, fun w hw => (hf w hw).1⟩
  obtain ⟨T, hTC, hmin⟩ := Finset.exists_min_image C Finset.card ⟨S, hCS⟩
  have hT := Finset.mem_filter.mp hTC
  have hTS : T ⊆ S := Finset.mem_powerset.mp hT.1
  have hTne : T.Nonempty := hT.2.1
  have hclosed : ∀ w ∈ T, f w ∈ T := hT.2.2
  have himsub : T.image f ⊆ T := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
    exact hclosed u hu
  have himC : T.image f ∈ C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (himsub.trans hTS), hTne.image f, ?_⟩
    intro w hw
    exact Finset.mem_image.mpr ⟨w, himsub hw, rfl⟩
  have him : T.image f = T :=
    Finset.eq_of_subset_of_card_le himsub (hmin _ himC)
  let fT : T → T := fun w => ⟨f w, hclosed w w.2⟩
  have hsurj : Function.Surjective fT := by
    intro w
    have hw : w.1 ∈ T.image f := him.symm ▸ w.2
    obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hw
    exact ⟨⟨u, hu⟩, Subtype.ext hfu⟩
  let p : Equiv.Perm T := Equiv.ofBijective fT
    ⟨(Finite.injective_iff_surjective).mpr hsurj, hsurj⟩
  let q : Equiv.Perm W := Equiv.Perm.ofSubtype p
  have hq_mem : ∀ w (hw : w ∈ T), q w = f w := by
    intro w hw
    exact Equiv.Perm.ofSubtype_apply_of_mem p hw
  have hq_not : ∀ w ∉ T, q w = w := fun w hw =>
    Equiv.Perm.ofSubtype_apply_of_not_mem p hw
  refine ⟨q, ?_, ?_, ?_⟩
  · intro w
    by_cases hw : w ∈ T
    · exact Or.inr ((hq_mem w hw).symm ▸ (hf w (hTS hw)).2)
    · exact Or.inl (hq_not w hw)
  · intro heq
    obtain ⟨w, hw⟩ := hTne
    have hfw : f w = w := (hq_mem w hw).symm.trans (congrArg (fun p => p w) heq)
    have hbad := (hf w (hTS hw)).2
    rw [hfw] at hbad
    exact hirr w hbad
  · intro w hw
    exact hq_not w (fun ht => hw (hTS ht))

/-- Under the exchange obstruction, every everywhere-supported successor
function is bijective. -/
theorem supported_function_bijective (R : W → W → Prop)
    (hirr : ∀ w, ¬ R w w) (hpartial : NoPartialPermutations R)
    (f : W → W) (hf : ∀ w, R w (f w)) : Function.Bijective f := by
  classical
  by_cases hW : Nonempty W
  · letI := hW
    obtain ⟨q, hq, hne, _⟩ := sinkfree_supported_permutation
      (fun w u => u = f w) (fun w hw => by
        have hbad := hf w
        rw [← hw] at hbad
        exact hirr w hbad)
      Finset.univ (Finset.univ_nonempty) (fun w _ => ⟨f w, Finset.mem_univ _, rfl⟩)
    have hqR : ∀ w, q w = w ∨ R w (q w) := by
      intro w
      rcases hq w with hfix | heq
      · exact Or.inl hfix
      · exact Or.inr (heq.symm ▸ hf w)
    have hqf : ∀ w, q w = f w := by
      intro w
      rcases hq w with hfix | heq
      · exact False.elim (hne (hpartial q hqR ⟨w, hfix⟩))
      · exact heq
    have heq : (q : W → W) = f := funext hqf
    exact heq ▸ q.bijective
  · letI : IsEmpty W := not_nonempty_iff.mp hW
    exact ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

/-- If there is no sink, the only possible outgoing neighbor is the chosen successor. -/
theorem sinkfree_outdegree_one (R : W → W → Prop) [DecidableRel R]
    (hirr : ∀ w, ¬ R w w) (hpartial : NoPartialPermutations R)
    (hout : ∀ w, ∃ u, R w u) (w : W) :
    (Finset.univ.filter (R w)).card = 1 := by
  classical
  choose f hf using hout
  have hbij := supported_function_bijective R hirr hpartial f hf
  have huniq : ∀ u, R w u → u = f w := by
    intro u hu
    let g := Function.update f w u
    have hg : ∀ x, R x (g x) := by
      intro x
      by_cases hx : x = w
      · subst x
        simpa only [g, Function.update_self] using hu
      · simpa only [g, Function.update_of_ne hx] using hf x
    have hginj := (supported_function_bijective R hirr hpartial g hg).1
    obtain ⟨z, hz⟩ := hbij.2 u
    by_cases hzw : z = w
    · simpa only [hzw] using hz.symm
    · have hgz : g z = g w := by simp [g, hzw, hz]
      exact False.elim (hzw (hginj hgz))
  have hset : Finset.univ.filter (R w) = {f w} := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    exact ⟨huniq u, fun h => h.symm ▸ hf w⟩
  rw [hset, Finset.card_singleton]

/-- Every nonempty induced subgraph has a sink. -/
def HereditarySink (R : W → W → Prop) (S : Finset W) : Prop :=
  ∀ T ⊆ S, T.Nonempty → ∃ w ∈ T, ∀ u ∈ T, ¬ R w u

theorem hereditarySink_of_sink (R : W → W → Prop)
    (hirr : ∀ w, ¬ R w w) (hpartial : NoPartialPermutations R)
    (v : W) (hsink : ∀ u, ¬ R v u) : HereditarySink R Finset.univ := by
  classical
  intro S _ hS
  by_contra! h
  obtain ⟨q, hq, hne, _⟩ := sinkfree_supported_permutation R hirr S hS h
  apply hne
  apply hpartial q hq
  refine ⟨v, ?_⟩
  exact (hq v).resolve_right (hsink (q v))

/-- A shifted finite harmonic sum, useful for the sink-removal induction. -/
def shiftedHarmonic (k : ℝ) (m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range m, 1 / (k + j)

theorem shiftedHarmonic_succ (k : ℝ) (m : ℕ) :
    shiftedHarmonic k (m + 1) = 1 / k + shiftedHarmonic (k + 1) m := by
  unfold shiftedHarmonic
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero, add_zero]
  rw [add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  ring

/-- Removing sinks gives the harmonic lower bound, including any positive shift. -/
theorem hereditarySink_reciprocal (R : W → W → Prop) [DecidableRel R]
    (S : Finset W) (hS : HereditarySink R S) (k : ℝ) (hk : 0 < k) :
    shiftedHarmonic k S.card ≤
      ∑ w ∈ S, 1 / (k + ((S.filter (R w)).card : ℝ)) := by
  classical
  induction S using Finset.strongInductionOn generalizing k with
  | _ S ih =>
    by_cases hne : S.Nonempty
    · obtain ⟨v, hv, hsink⟩ := hS S (Finset.Subset.refl _) hne
      let T := S.erase v
      have hTsub : T ⊂ S := Finset.erase_ssubset hv
      have hT : HereditarySink R T := by
        intro U hUT hUne
        exact hS U (hUT.trans (Finset.erase_subset _ _)) hUne
      have hind := ih T hTsub hT (k + 1) (by linarith)
      have hdegree_v : S.filter (R v) = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro w hw
        exact hsink w (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
      have hcard : S.card = T.card + 1 := by
        exact (Finset.card_erase_add_one hv).symm
      have hsum : (∑ w ∈ S, 1 / (k + ((S.filter (R w)).card : ℝ))) =
          1 / k + ∑ w ∈ T, 1 / (k + ((S.filter (R w)).card : ℝ)) := by
        rw [← Finset.add_sum_erase S (fun w => 1 / (k + ((S.filter (R w)).card : ℝ))) hv]
        simp only [hdegree_v, Finset.card_empty, Nat.cast_zero, add_zero]
        rfl
      have hterm : ∀ w ∈ T,
          1 / (k + 1 + ((T.filter (R w)).card : ℝ)) ≤
            1 / (k + ((S.filter (R w)).card : ℝ)) := by
        intro w hw
        have hdeg : (S.filter (R w)).card ≤ (T.filter (R w)).card + 1 := by
          have hset : S = insert v T := (Finset.insert_erase hv).symm
          rw [hset, Finset.filter_insert]
          split_ifs
          · exact Finset.card_insert_le _ _
          · exact Nat.le_succ _
        have hdegr : ((S.filter (R w)).card : ℝ) ≤
            ((T.filter (R w)).card : ℝ) + 1 := by exact_mod_cast hdeg
        apply one_div_le_one_div_of_le (by positivity)
        linarith
      rw [hcard, shiftedHarmonic_succ, hsum]
      exact add_le_add (le_refl _) (hind.trans (Finset.sum_le_sum hterm))
    · have hempty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst S
      simp [shiftedHarmonic]

/-- The usual harmonic sum `1 + 1/2 + ... + 1/m`. -/
def harmonic (m : ℕ) : ℝ := shiftedHarmonic 1 m

/-- The coefficient in Theorem 4.1, including its special value at one edge. -/
def beta (m : ℕ) : ℝ := if m = 1 then 1 else min ((m : ℝ) / ((2 : ℕ) : ℝ)) (harmonic m)

theorem beta_le_harmonic (m : ℕ) : beta m ≤ harmonic m := by
  by_cases hm : m = 1
  · subst m
    simp [beta, harmonic, shiftedHarmonic]
  · exact (if_neg hm).trans_le (min_le_right _ _)

/-- The reciprocal outdegree inequality required by the harmonic shadow proof. -/
theorem reciprocal_outdegree_bound (R : W → W → Prop) [DecidableRel R]
    (hirr : ∀ w, ¬ R w w) (hpartial : NoPartialPermutations R) :
    beta (Fintype.card W) ≤
      ∑ w : W, 1 / (1 + ((Finset.univ.filter (R w)).card : ℝ)) := by
  classical
  by_cases hout : ∀ w, ∃ u, R w u
  · have hc : Fintype.card W ≠ 1 := by
      intro hc
      obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.mp hc
      obtain ⟨u, hu⟩ := hout w
      exact hirr w (hw u ▸ hu)
    have hsum : (∑ w : W, 1 / (1 + ((Finset.univ.filter (R w)).card : ℝ))) =
        (Fintype.card W : ℝ) / 2 := by
      simp only [sinkfree_outdegree_one R hirr hpartial hout,
        Nat.cast_one, one_add_one_eq_two, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring
    rw [hsum, beta, if_neg hc]
    exact min_le_left _ _
  · obtain ⟨v, hv⟩ := not_forall.mp hout
    have hsink : ∀ u, ¬ R v u := fun u hu => hv ⟨u, hu⟩
    have hh := hereditarySink_reciprocal R Finset.univ
      (hereditarySink_of_sink R hirr hpartial v hsink) 1 (by norm_num)
    simpa only [Finset.card_univ] using (beta_le_harmonic (Fintype.card W)).trans hh

variable {V I : Type*} [DecidableEq V] [Fintype I] {H : Hypergraph V}

/-- The paper's reciprocal bound derived from ordinary hypergraph rigidity. -/
theorem rigid_exchange_reciprocal_bound (G : RigidFamily H I) (i : I)
    (rep : G.matching i → V) (hrep : ∀ e, rep e ∈ e.1)
    (hsize : ∀ e : G.matching i, 2 ≤ e.1.card) :
    beta (G.matching i).card ≤
      ∑ e : G.matching i,
        1 / (1 + ((Finset.univ.filter (exchangeArc H rep e)).card : ℝ)) := by
  classical
  simpa only [Fintype.card_coe] using reciprocal_outdegree_bound (exchangeArc H rep)
    (fun e he => he.1 rfl) (rigid_exchange_noPartialPermutations G i rep hrep hsize)

end RigidGHZ.UpperBounds
