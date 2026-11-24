module

public import RigidGHZ.Relabel
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Tactic.FinCases

@[expose] public section

namespace RigidGHZ.Finite

def pairCompletions (H : Hypergraph (Fin 9)) (a b : Fin 9) : Finset (Fin 9) :=
  Finset.univ.filter (fun x => x ≠ a ∧ x ≠ b ∧ ({a, b, x} : Finset (Fin 9)) ∈ H)

theorem pairCompletions_card_le_seven (H : Hypergraph (Fin 9)) {a b : Fin 9}
    (hab : a ≠ b) : (pairCompletions H a b).card ≤ 7 := by
  have ha : a ∉ pairCompletions H a b := by simp [pairCompletions]
  have hb : b ∉ pairCompletions H a b := by simp [pairCompletions]
  have h := Finset.card_le_card
    (Finset.subset_univ (insert a (insert b (pairCompletions H a b))))
  simp [ha, hb, hab] at h
  omega

theorem normalize_two_points_and_set {a b : Fin 9} (hab : a ≠ b)
    (X : Finset (Fin 9)) (ha : a ∉ X) (hb : b ∉ X) :
    ∃ f : Equiv.Perm (Fin 9), f a = 0 ∧ f b = 1 ∧
      ∀ x, x ∈ X ↔ 2 ≤ (f x).val ∧ (f x).val < 2 + X.card := by
  classical
  have hcard : 2 + X.card ≤ 9 := by
    have h := Finset.card_le_card (Finset.subset_univ (insert a (insert b X)))
    simp [ha, hb, hab] at h
    omega
  let e : ↥X ≃ Fin X.card := X.equivFin
  let u : Fin 2 ⊕ Fin X.card → Fin 9 := fun s =>
    match s with
    | Sum.inl i => if i = 0 then a else b
    | Sum.inr j => (e.symm j).val
  let v : Fin 2 ⊕ Fin X.card → Fin 9 := fun s =>
    ⟨(finSumFinEquiv s).val, lt_of_lt_of_le (finSumFinEquiv s).isLt hcard⟩
  have hu : Function.Injective u := by
    intro s t h
    cases s with
    | inl i =>
      cases t with
      | inl j =>
        fin_cases i <;> fin_cases j <;> simp_all [u, Ne.symm hab]
      | inr j =>
        have hx := (e.symm j).property
        fin_cases i <;> simp only [u] at h
        · simp at h
          exact False.elim (ha (h ▸ hx))
        · simp at h
          exact False.elim (hb (h ▸ hx))
    | inr i =>
      cases t with
      | inl j =>
        have hx := (e.symm i).property
        fin_cases j <;> simp only [u] at h
        · simp at h
          exact False.elim (ha (h ▸ hx))
        · simp at h
          exact False.elim (hb (h ▸ hx))
      | inr j =>
        have hij : i = j := e.symm.injective (Subtype.ext h)
        exact congrArg Sum.inr hij
  have hv : Function.Injective v := by
    intro s t h
    apply finSumFinEquiv.injective
    apply Fin.ext
    exact congrArg (Fin.val : Fin 9 → ℕ) h
  obtain ⟨f, hf⟩ := Equiv.Perm.exists_extending_pair u v hu hv
  have hfa : f a = 0 := by simpa [u, v] using hf (Sum.inl 0)
  have hfb : f b = 1 := by simpa [u, v] using hf (Sum.inl 1)
  have hfx : ∀ j : Fin X.card, (f (e.symm j).val).val = 2 + j.val := by
    intro j
    have h := congrArg Fin.val (hf (Sum.inr j))
    simpa [u, v] using h
  refine ⟨f, hfa, hfb, ?_⟩
  intro x
  constructor
  · intro hx
    have h := hfx (e ⟨x, hx⟩)
    simp only [Equiv.symm_apply_apply] at h
    have hj := (e ⟨x, hx⟩).isLt
    omega
  · rintro ⟨hx0, hx1⟩
    let j : Fin X.card := ⟨(f x).val - 2, by omega⟩
    have hj := hfx j
    have hf' : f (e.symm j).val = f x := by
      apply Fin.ext
      have hjv : j.val = (f x).val - 2 := rfl
      omega
    have he := f.injective hf'
    exact he ▸ (e.symm j).property

/-- Normalize a pair and every one of its completions. The result is the
canonical finite instance consumed by the nine-vertex upper-bound checker. -/
theorem normalize_pair (H : Hypergraph (Fin 9)) {a b : Fin 9} (hab : a ≠ b) :
    ∃ f : Equiv.Perm (Fin 9), f a = 0 ∧ f b = 1 ∧
      ∀ x : Fin 9, x ≠ 0 → x ≠ 1 →
        (({0, 1, x} : Finset (Fin 9)) ∈ relabelHypergraph f H ↔
          2 ≤ x.val ∧ x.val < 2 + (pairCompletions H a b).card) := by
  have ha : a ∉ pairCompletions H a b := by simp [pairCompletions]
  have hb : b ∉ pairCompletions H a b := by simp [pairCompletions]
  obtain ⟨f, hfa, hfb, hfX⟩ := normalize_two_points_and_set hab
    (pairCompletions H a b) ha hb
  refine ⟨f, hfa, hfb, ?_⟩
  intro x hx0 hx1
  have hxa : f.symm x ≠ a := by
    intro h
    apply hx0
    rw [← hfa, ← h, Equiv.apply_symm_apply]
  have hxb : f.symm x ≠ b := by
    intro h
    apply hx1
    rw [← hfb, ← h, Equiv.apply_symm_apply]
  have he : relabelEdge f ({a, b, f.symm x} : Finset (Fin 9)) = {0, 1, x} := by
    simp [relabelEdge, hfa, hfb]
  rw [← he, relabelEdge_mem_relabelHypergraph]
  have h := hfX (f.symm x)
  have hm : f.symm x ∈ pairCompletions H a b ↔ {a, b, f.symm x} ∈ H := by
    simp only [pairCompletions, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2.2, fun h => ⟨hxa, hxb, h⟩⟩
  rw [hm] at h
  simpa only [Equiv.apply_symm_apply] using h

end RigidGHZ.Finite
