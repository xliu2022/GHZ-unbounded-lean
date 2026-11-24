module

public import RigidGHZ.Finite.NineParallelClasses

/-! Translation orbits and cosets in each nonzero sum class.

The certificates below inspect only the nine actual edges of a fixed sum class
and the nine points of the affine plane.  Statements quantified over arbitrary
matchings or arbitrary finite sets of translation vectors are deduced from
these certificates by ordinary set and cardinality arguments. -/

@[expose] public section

namespace RigidGHZ.Finite

local instance translatePerfectDecidable (σ : AffinePlane) (M : Hypergraph AffinePlane) :
    Decidable (PerfectMatching (sumClass σ) M) := by
  unfold PerfectMatching
  infer_instance

/-- The actual translate `T + x`. -/
def translateEdge (T : Finset AffinePlane) (x : AffinePlane) : Finset AffinePlane :=
  T.image (fun v => v + x)

/-- The actual difference set `T - T`, including zero. -/
def edgeDifferences (T : Finset AffinePlane) : Finset AffinePlane :=
  (T.product T).image (fun p => p.1 - p.2)

/-- Translate `T` by the points of the coset `a + ⟨σ⟩`. -/
def translatedCosetMatching (T : Finset AffinePlane) (σ a : AffinePlane) :
    Hypergraph AffinePlane :=
  (affineLine a σ).image (translateEdge T)

def translatedCosetMatchings (T : Finset AffinePlane) (σ : AffinePlane) :
    Finset (Hypergraph AffinePlane) :=
  (affineParallelClass σ).image (fun A => A.image (translateEdge T))

/-- A small local certificate, quantified only over members of the nine-edge
sum class. Splitting its eight instances bounds kernel-checking memory. -/
def NonzeroSumCertificate (σ : AffinePlane) : Prop :=
  ∀ T ∈ sumClass σ,
    Finset.univ.image (translateEdge T) = sumClass σ ∧
    (edgeDifferences T).erase 0 = Finset.univ \ {0, σ, -σ} ∧
    ∀ a : AffinePlane, PerfectMatching (sumClass σ) (translatedCosetMatching T σ a)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_01 : NonzeroSumCertificate (0, 1) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_02 : NonzeroSumCertificate (0, 2) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_10 : NonzeroSumCertificate (1, 0) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_11 : NonzeroSumCertificate (1, 1) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_12 : NonzeroSumCertificate (1, 2) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_20 : NonzeroSumCertificate (2, 0) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_21 : NonzeroSumCertificate (2, 1) := by
  unfold NonzeroSumCertificate
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
theorem nonzeroSumCertificate_22 : NonzeroSumCertificate (2, 2) := by
  unfold NonzeroSumCertificate
  decide +kernel

theorem nonzero_sum_certificate {σ : AffinePlane} (hσ : σ ≠ 0) :
    NonzeroSumCertificate σ := by
  have hcases : ∀ σ : AffinePlane, σ ≠ 0 →
      σ = (0, 1) ∨ σ = (0, 2) ∨ σ = (1, 0) ∨ σ = (1, 1) ∨
      σ = (1, 2) ∨ σ = (2, 0) ∨ σ = (2, 1) ∨ σ = (2, 2) := by
    decide +kernel
  rcases hcases σ hσ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact nonzeroSumCertificate_01
  · exact nonzeroSumCertificate_02
  · exact nonzeroSumCertificate_10
  · exact nonzeroSumCertificate_11
  · exact nonzeroSumCertificate_12
  · exact nonzeroSumCertificate_20
  · exact nonzeroSumCertificate_21
  · exact nonzeroSumCertificate_22

/-- Any edge in a nonzero sum class generates the whole class by translation. -/
theorem sumClass_nonzero_eq_translates {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    sumClass σ = Finset.univ.image (translateEdge T) :=
  ((nonzero_sum_certificate hσ) T hT).1.symm

/-- All nine translates are distinct. -/
theorem translateEdge_injective {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    Function.Injective (translateEdge T) := by
  have hc : (Finset.univ.image (translateEdge T)).card =
      (Finset.univ : Finset AffinePlane).card := by
    rw [← sumClass_nonzero_eq_translates hσ hT, sumClass_card, ite_eq_right hσ]
    norm_num [AffinePlane, Fintype.card_prod, ZMod.card]
  intro x y hxy
  exact (Finset.card_image_iff.mp hc) (Finset.mem_univ x) (Finset.mem_univ y) hxy

/-- The displayed difference-set identity holds for every edge of the class,
not only the particular triangle chosen in the paper. -/
theorem nonzero_sum_difference_set {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    (edgeDifferences T).erase 0 = Finset.univ \ {0, σ, -σ} :=
  ((nonzero_sum_certificate hσ) T hT).2.1

/-- The elementary bridge from a difference set to intersection of translates. -/
theorem translateEdge_disjoint_iff (T : Finset AffinePlane) (x y : AffinePlane) :
    Disjoint (translateEdge T x) (translateEdge T y) ↔ x - y ∉ edgeDifferences T := by
  rw [Finset.disjoint_left]
  constructor
  · intro hd hm
    obtain ⟨⟨a, b⟩, hab, heq⟩ := Finset.mem_image.mp hm
    obtain ⟨ha, hb⟩ := Finset.mem_product.mp hab
    have heq' : a - b = x - y := heq
    have hc : b + x = a + y := by
      calc
        b + x = (x - y) + b + y := by abel
        _ = (a - b) + b + y := by rw [← heq']
        _ = a + y := by abel
    exact hd (Finset.mem_image.mpr ⟨b, hb, rfl⟩)
      (Finset.mem_image.mpr ⟨a, ha, hc.symm⟩)
  · intro hd z hz₁ hz₂
    obtain ⟨a, ha, hax⟩ := Finset.mem_image.mp hz₁
    obtain ⟨b, hb, hby⟩ := Finset.mem_image.mp hz₂
    apply hd
    refine Finset.mem_image.mpr ⟨(b, a), Finset.mem_product.mpr ⟨hb, ha⟩, ?_⟩
    change b - a = x - y
    calc
      b - a = (b + y) - (a + x) + (x - y) := by abel
      _ = x - y := by rw [hby, hax]; simp

/-- Distinct translates are disjoint exactly for the two nonzero differences
in the direction generated by their sum. -/
theorem nonzero_translates_disjoint_iff {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ)
    {x y : AffinePlane} (hxy : x ≠ y) :
    Disjoint (translateEdge T x) (translateEdge T y) ↔ x - y = σ ∨ x - y = -σ := by
  rw [translateEdge_disjoint_iff]
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have hm : x - y ∈ edgeDifferences T ↔
      x - y ∈ (Finset.univ \ {0, σ, -σ} : Finset AffinePlane) := by
    have h := congrArg (fun A : Finset AffinePlane => x - y ∈ A)
      (nonzero_sum_difference_set hσ hT)
    simpa [hne] using (Iff.of_eq h)
  rw [hm]
  simp only [Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  tauto

theorem translatedCosetMatching_perfect {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) (a : AffinePlane) :
    PerfectMatching (sumClass σ) (translatedCosetMatching T σ a) :=
  ((nonzero_sum_certificate hσ) T hT).2.2 a

theorem mem_translatedCosetMatchings (T : Finset AffinePlane) (σ : AffinePlane)
    (M : Hypergraph AffinePlane) :
    M ∈ translatedCosetMatchings T σ ↔ ∃ a, M = translatedCosetMatching T σ a := by
  unfold translatedCosetMatchings affineParallelClass
  rw [Finset.image_image]
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  exact exists_congr fun _ => eq_comm

theorem translatedCosetMatchings_card {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    (translatedCosetMatchings T σ).card = 3 := by
  unfold translatedCosetMatchings
  rw [Finset.card_image_of_injective _
    (Finset.image_injective (translateEdge_injective hσ hT))]
  exact affineParallelClass_card hσ

/-- Equality of the actual finite sets of ordinary matchings. -/
theorem sumClass_nonzero_matchings_eq_cosets {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    sumClassMatchings σ = translatedCosetMatchings T σ := by
  have hsub : translatedCosetMatchings T σ ⊆ sumClassMatchings σ := by
    intro M hM
    obtain ⟨a, rfl⟩ := (mem_translatedCosetMatchings T σ M).mp hM
    exact (mem_sumClassMatchings σ _).mpr (translatedCosetMatching_perfect hσ hT a)
  have hleft : (sumClassMatchings σ).card = 3 := by
    simpa only [ite_eq_right hσ] using sumClassMatchings_card σ
  have hright := translatedCosetMatchings_card hσ hT
  exact (Finset.eq_of_subset_of_card_le hsub (by omega)).symm

theorem sumClass_nonzero_perfect_iff_coset {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) (M : Hypergraph AffinePlane) :
    PerfectMatching (sumClass σ) M ↔ ∃ a, M = translatedCosetMatching T σ a := by
  rw [← mem_sumClassMatchings, sumClass_nonzero_matchings_eq_cosets hσ hT]
  exact mem_translatedCosetMatchings T σ M

/-- The exact criterion on the translation vectors, for an arbitrary finite
set `X`: its translates form an ordinary perfect matching iff `X` is a coset
`{a + tσ : t ∈ 𝔽₃}`. No bound on `X` is assumed. -/
theorem translates_perfect_iff_vector_coset {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) (X : Finset AffinePlane) :
    PerfectMatching (sumClass σ) (X.image (translateEdge T)) ↔
      ∃ a, X = affineLine a σ := by
  rw [sumClass_nonzero_perfect_iff_coset hσ hT]
  exact exists_congr fun _ => Finset.image_inj (translateEdge_injective hσ hT)

/-- The cosets, used as labels, give exactly the three disjoint matching
classes and all nine edges in a nonzero sum class. -/
def nonzeroCosetFamily {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) :
    RigidFamily (sumClass σ) ↥(affineParallelClass σ) where
  matching := fun A => A.val.image (translateEdge T)
  perfect := by
    intro A
    obtain ⟨a, _, ha⟩ := Finset.mem_image.mp A.property
    rw [← ha]
    exact translatedCosetMatching_perfect hσ hT a
  edge_disjoint := by
    intro A B hne
    have hAB : Disjoint A.val B.val := (affineParallelClass_partition hσ).1
      A.val A.property B.val B.property (fun h => hne (Subtype.ext h))
    apply Finset.disjoint_left.mpr
    intro e heA heB
    obtain ⟨x, hx, hxe⟩ := Finset.mem_image.mp heA
    obtain ⟨y, hy, hye⟩ := Finset.mem_image.mp heB
    have hxy : x = y := translateEdge_injective hσ hT (hxe.trans hye.symm)
    exact Finset.disjoint_left.mp hAB hx (by simpa only [hxy] using hy)
  covers := by
    calc
      sumClass σ = (Finset.univ : Finset AffinePlane).image (translateEdge T) :=
        sumClass_nonzero_eq_translates hσ hT
      _ = ((affineParallelClass σ).biUnion id).image (translateEdge T) := by
        rw [← (affineParallelClass_partition hσ).2]
      _ = (affineParallelClass σ).biUnion (fun A => A.image (translateEdge T)) :=
        Finset.biUnion_image
      _ = (Finset.univ : Finset ↥(affineParallelClass σ)).biUnion
          (fun A => A.val.image (translateEdge T)) := by
        rw [Finset.univ_eq_attach, Finset.attach_biUnion]
  complete := by
    intro M hM
    obtain ⟨a, ha⟩ := (sumClass_nonzero_perfect_iff_coset hσ hT M).mp hM
    exact ⟨⟨affineLine a σ, Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩⟩, ha⟩

theorem sumClass_nonzero_rigid {σ : AffinePlane} (hσ : σ ≠ 0)
    {T : Finset AffinePlane} (hT : T ∈ sumClass σ) : IsRigid (sumClass σ) 3 := by
  have hc : Fintype.card ↥(affineParallelClass σ) = 3 := by
    rw [Fintype.card_coe]
    exact affineParallelClass_card hσ
  exact ⟨(nonzeroCosetFamily hσ hT).reindex (Fintype.equivFinOfCardEq hc).symm⟩

/-- The particular triangle `T={0,u,σ-u}` used in the paper. -/
def sumTriangle (σ u : AffinePlane) : Finset AffinePlane := {0, u, σ - u}

theorem exists_outside_sum_direction {σ : AffinePlane} (hσ : σ ≠ 0) :
    ∃ u : AffinePlane, u ∉ affineLine 0 σ := by
  have h : ∀ σ : AffinePlane, σ ≠ 0 → ∃ u : AffinePlane, u ∉ affineLine 0 σ := by
    decide +kernel
  exact h σ hσ

theorem sumTriangle_mem {σ u : AffinePlane} (hσ : σ ≠ 0)
    (hu : u ∉ affineLine 0 σ) : sumTriangle σ u ∈ sumClass σ := by
  have h : ∀ σ u : AffinePlane, σ ≠ 0 →
      u ∉ affineLine 0 σ → sumTriangle σ u ∈ sumClass σ := by
    decide +kernel
  exact h σ u hσ hu

/-- Each sum class has the exact ordinary rigidity asserted in the affine
description: four parallel classes at zero and three coset classes elsewhere. -/
theorem sumClass_rigid (σ : AffinePlane) :
    IsRigid (sumClass σ) (if σ = 0 then 4 else 3) := by
  by_cases hσ : σ = 0
  · subst σ
    simpa using sumClass_zero_rigid
  · obtain ⟨u, hu⟩ := exists_outside_sum_direction hσ
    simpa only [ite_eq_right hσ] using
      sumClass_nonzero_rigid hσ (sumTriangle_mem hσ hu)

end RigidGHZ.Finite
