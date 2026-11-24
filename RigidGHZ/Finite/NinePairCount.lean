module

public import RigidGHZ.Finite.PairNormalization
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

@[expose] public section
namespace RigidGHZ.Finite
open scoped BigOperators

 theorem triple_through_pair {e : Finset (Fin 9)} (he : e.card = 3)
    {a b : Fin 9} (hab : a ≠ b) (ha : a ∈ e) (hb : b ∈ e) :
    ∃ x, x ≠ a ∧ x ≠ b ∧ e = {a,b,x} := by
  have hsub : ({a,b} : Finset (Fin 9)) ⊆ e := by
    intro x hx
    rcases (by simpa only [Finset.mem_insert,Finset.mem_singleton] using hx : x = a ∨ x = b) with rfl | rfl
    · exact ha
    · exact hb
  have hc : (e \ {a,b}).card = 1 := by
    rw [Finset.card_sdiff_of_subset hsub,he]
    simp [hab]
  obtain ⟨x,hx⟩ := Finset.card_eq_one.mp hc
  have hxmem : x ∈ e \ {a,b} := by rw [hx]; simp
  have hxne : x ≠ a ∧ x ≠ b := by
    simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using (Finset.mem_sdiff.mp hxmem).2
  refine ⟨x,hxne.1,hxne.2,?_⟩
  have hh := Finset.union_sdiff_of_subset hsub
  rw [hx] at hh
  calc
    e = {a,b} ∪ {x} := hh.symm
    _ = {a,b,x} := by ext y; simp [or_assoc]

 theorem pairCompletions_card_eq {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    {a b : Fin 9} (hab : a ≠ b) :
    (pairCompletions H a b).card = (H.filter (fun e => a ∈ e ∧ b ∈ e)).card := by
  let f : Fin 9 → Finset (Fin 9) := fun x => {a,b,x}
  have hinj : Set.InjOn f (↑(pairCompletions H a b) : Set (Fin 9)) := by
    intro x hx y hy hxy
    have hxne := (Finset.mem_filter.mp hx).2
    have hh : x ∈ f y := by rw [←hxy]; simp [f]
    simpa [f,hxne.1,hxne.2.1] using hh
  have himage : (pairCompletions H a b).image f = H.filter (fun e => a ∈ e ∧ b ∈ e) := by
    ext e
    constructor
    · intro he
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).2.2.2,by simp [f]⟩
    · intro he
      obtain ⟨heH,ha,hb⟩ := Finset.mem_filter.mp he
      obtain ⟨x,hxa,hxb,rfl⟩ := triple_through_pair (hU e heH) hab ha hb
      exact Finset.mem_image.mpr ⟨x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxa,hxb,heH⟩,rfl⟩
  exact (Finset.card_image_of_injOn hinj).symm.trans (congrArg Finset.card himage)

/-- Double counting the two other vertices of every edge through a fixed vertex. -/
theorem pairCompletions_sum {H : Hypergraph (Fin 9)} (hU : Uniform H 3) (a : Fin 9) :
    (∑ b ∈ Finset.univ.erase a, (pairCompletions H a b).card) = 2 * degree H a := by
  classical
  let A := H.filter (fun e => a ∈ e)
  have hd := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
    (fun b (e : Finset (Fin 9)) => b ∈ e) (s := Finset.univ.erase a) (t := A)
  have hleft : (∑ b ∈ Finset.univ.erase a, (pairCompletions H a b).card) =
      ∑ b ∈ Finset.univ.erase a, (A.filter (fun e => b ∈ e)).card := by
    apply Finset.sum_congr rfl
    intro b hb
    have hba : b ≠ a := (Finset.mem_erase.mp hb).1
    rw [pairCompletions_card_eq hU (Ne.symm hba)]
    congr 1
    ext e
    simp [A,and_assoc]
  have hright : (∑ e ∈ A, ((Finset.univ.erase a).filter (fun b => b ∈ e)).card) = 2 * degree H a := by
    have hc : ∀ e ∈ A, ((Finset.univ.erase a).filter (fun b => b ∈ e)).card = 2 := by
      intro e he
      have hea := Finset.mem_filter.mp he
      have heq : (Finset.univ.erase a).filter (fun b => b ∈ e) = e.erase a := by
        ext b
        simp [and_comm]
      rw [heq,Finset.card_erase_of_mem hea.2,hU e hea.1]
    calc
      _ = ∑ _e ∈ A, 2 := Finset.sum_congr rfl hc
      _ = 2 * degree H a := by simp [A,degree,Nat.mul_comm]
  exact hleft.trans (hd.trans hright)

 theorem fourteen_has_pair_four {H : Hypergraph (Fin 9)} (hU : Uniform H 3)
    (F : RigidFamily H (Fin 14)) :
    ∃ a b : Fin 9, a ≠ b ∧ 4 ≤ (pairCompletions H a b).card := by
  have hs := pairCompletions_sum hU 0
  rw [F.regular] at hs
  simp only [Fintype.card_fin] at hs
  by_contra hn
  have hb : ∀ b ∈ (Finset.univ.erase (0 : Fin 9)), (pairCompletions H 0 b).card ≤ 3 := by
    intro b hb
    have hb0 : b ≠ 0 := (Finset.mem_erase.mp hb).1
    have hlt : ¬4 ≤ (pairCompletions H 0 b).card := by
      intro h
      exact hn ⟨0,b,Ne.symm hb0,h⟩
    omega
  have hsum := Finset.sum_le_sum hb
  have hcard : (Finset.univ.erase (0 : Fin 9)).card = 8 := by decide
  simp only [Finset.sum_const,smul_eq_mul,hcard] at hsum
  omega

end RigidGHZ.Finite
