module

public import RigidGHZ.Supplement.Periodic.Trace
public import RigidGHZ.Supplement.Periodic.MatrixHeight
public import RigidGHZ.Supplement.Periodic.Rigidity

/-! From finite local-configuration certificates to exact matrix multiplicities. -/

@[expose] public section

namespace RigidGHZ.Supplement.Periodic.Scheme

variable {V E I : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]
  [Fintype I] [DecidableEq I] (D : Scheme V E)

 theorem transferMatrix_nonzero_iff (s t : Finset V) : D.transferMatrix s t ≠ 0 ↔
    ∃ A, D.LocalConfig A ∧ D.input A = s ∧ D.output A = t := by
  change Fintype.card (WeightedWalks.Arc (fun A : D.Configurations => D.input A.1)
    (fun A : D.Configurations => D.output A.1) s t) ≠ 0 ↔ _
  rw [← Nat.pos_iff_ne_zero, Fintype.card_pos_iff]
  constructor
  · rintro ⟨⟨⟨A, hA⟩, hs, ht⟩⟩
    exact ⟨A, hA, hs, ht⟩
  · rintro ⟨A, hA, hs, ht⟩
    exact ⟨⟨⟨A, hA⟩, hs, ht⟩⟩

 theorem transferMatrix_eq_catalog (s t : Finset V) (K : Finset (Finset E))
    (hvalid : ∀ A ∈ K, D.LocalConfig A)
    (hcat : ∀ A, D.LocalConfig A → (D.input A = s ∧ D.output A = t ↔ A ∈ K)) :
    D.transferMatrix s t = K.card := by
  classical
  let e : WeightedWalks.Arc (fun A : D.Configurations => D.input A.1)
      (fun A : D.Configurations => D.output A.1) s t ≃ {A // A ∈ K} :=
    { toFun := fun A => ⟨A.1.1, (hcat A.1.1 A.1.2).mp A.2⟩
      invFun := fun A => ⟨⟨A.1, hvalid A.1 A.2⟩, (hcat A.1 (hvalid A.1 A.2)).mpr A.2⟩
      left_inv := by intro A; apply Subtype.ext; apply Subtype.ext; rfl
      right_inv := by intro A; apply Subtype.ext; rfl }
  change Fintype.card (WeightedWalks.Arc (fun A : D.Configurations => D.input A.1)
    (fun A : D.Configurations => D.output A.1) s t) = K.card
  simpa only [Fintype.card_coe] using Fintype.card_congr e

 theorem diagonal_le_one (c : E → I)
    (hinj : Function.Injective (fun i => D.input (colorClass c i)))
    (hloops : ∀ A, D.LocalConfig A → D.input A = D.output A → ∃ i, A = colorClass c i)
    (s : Finset V) : D.transferMatrix s s ≤ 1 := by
  classical
  apply Fintype.card_le_one_iff_subsingleton.mpr
  constructor
  intro A B
  obtain ⟨i, hi⟩ := hloops A.1.1 A.1.2 (A.2.1.trans A.2.2.symm)
  obtain ⟨j, hj⟩ := hloops B.1.1 B.1.2 (B.2.1.trans B.2.2.symm)
  have hij : i = j := hinj (by
    change D.input (colorClass c i) = D.input (colorClass c j)
    rw [← hi, ← hj]
    exact A.2.1.trans B.2.1.symm)
  apply Subtype.ext
  apply Subtype.ext
  exact hi.trans ((congrArg (colorClass c) hij).trans hj.symm)

 theorem diagonal_zero (c : E → I)
    (hloops : ∀ A, D.LocalConfig A → D.input A = D.output A → ∃ i, A = colorClass c i)
    (s : Finset V) (havoid : ∀ i, D.input (colorClass c i) ≠ s) :
    D.transferMatrix s s = 0 := by
  by_contra hn
  obtain ⟨A, hA, hs, ht⟩ := (D.transferMatrix_nonzero_iff s s).mp hn
  obtain ⟨i, hi⟩ := hloops A hA (hs.trans ht.symm)
  exact havoid i (by simpa only [hi] using hs)

 theorem trace_eq_classes (c : E → I)
    (hlocal : ∀ i, D.LocalConfig (colorClass c i))
    (hloop : ∀ i, D.output (colorClass c i) = D.input (colorClass c i))
    (hinj : Function.Injective (fun i => D.input (colorClass c i)))
    (hloops : ∀ A, D.LocalConfig A → D.input A = D.output A → ∃ i, A = colorClass c i) :
    Matrix.trace D.transferMatrix = Fintype.card I := by
  classical
  let f : I → (s : Finset V) × WeightedWalks.Arc
      (fun A : D.Configurations => D.input A.1) (fun A : D.Configurations => D.output A.1) s s :=
    fun i => ⟨D.input (colorClass c i), ⟨⟨colorClass c i, hlocal i⟩, rfl, hloop i⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      exact hinj (congrArg Sigma.fst hij)
    · rintro ⟨s, ⟨⟨A, hA⟩, hs, ht⟩⟩
      obtain ⟨i, hi⟩ := hloops A hA (hs.trans ht.symm)
      subst A
      subst s
      refine ⟨i, ?_⟩
      apply Sigma.ext rfl
      apply heq_of_eq
      apply Subtype.ext
      apply Subtype.ext
      rfl
  have hc := Fintype.card_congr (Equiv.ofBijective f hf)
  rw [Fintype.card_sigma] at hc
  simpa only [transferMatrix, WeightedWalks.matrix, Matrix.trace, Matrix.diag] using hc.symm

 theorem blockTriangular_of_monotone (height : Finset V → ℕ)
    (hmono : ∀ A, D.LocalConfig A → height (D.input A) ≤ height (D.output A)) :
    D.transferMatrix.BlockTriangular height := by
  intro s t hts
  by_contra hn
  obtain ⟨A, hA, hs, ht⟩ := (D.transferMatrix_nonzero_iff s t).mp hn
  have h := hmono A hA
  rw [hs, ht] at h
  omega

 theorem strict_flat_zero (height : Finset V → ℕ)
    (hcert : ∀ A, D.LocalConfig A → D.input A = D.output A ∨
      height (D.input A) < height (D.output A))
    (s t : Finset V) (hst : height s = height t) (hne : s ≠ t) :
    D.transferMatrix s t = 0 := by
  by_contra hn
  obtain ⟨A, hA, hs, ht⟩ := (D.transferMatrix_nonzero_iff s t).mp hn
  have h := hcert A hA
  rw [hs, ht] at h
  rcases h with h | h
  · exact hne h
  · omega

 theorem exceptional_flat_zero (height : Finset V → ℕ) (x y : Finset V)
    (hcert : ∀ A, D.LocalConfig A → height (D.input A) = height (D.output A) →
      D.input A = D.output A ∨ (D.input A = x ∧ D.output A = y) ∨
      (D.input A = y ∧ D.output A = x))
    (s t : Finset V) (hst : height s = height t) (hne : s ≠ t)
    (hxy : ¬(s = x ∧ t = y)) (hyx : ¬(s = y ∧ t = x)) :
    D.transferMatrix s t = 0 := by
  by_contra hn
  obtain ⟨A, hA, hs, ht⟩ := (D.transferMatrix_nonzero_iff s t).mp hn
  have h := hcert A hA (by rwa [hs, ht])
  rw [hs, ht] at h
  exact h.elim hne (fun h => h.elim hxy hyx)

end RigidGHZ.Supplement.Periodic.Scheme
