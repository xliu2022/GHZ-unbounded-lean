module

public import RigidGHZ.Supplement.LinearSeedBank
public import RigidGHZ.Supplement.LinearResidueCertificates

/-! The five unconditional linear balanced thresholds of Supplement S7.
Each residue certificate uses actual rigid linear seeds, retains exactly the
target number of classes, and applies the proved ordinary graft construction. -/

@[expose] public section

namespace RigidGHZ.Supplement.LinearThresholds

open LinearSeeds LinearResidues

theorem available8 : ∀ x ∈ increments8, LinearSeed (x + 1) 8 := by
  intro x hx
  fin_cases hx
  · exact q8
  · exact q20
  · exact q21
  · exact q24
  · exact LinearSeed.restrict q26 (by decide) (by decide)
  · exact q30
  · exact LinearSeed.restrict q39 (by decide) (by decide)

theorem bounded8 (m : ℕ) (hm : 33 ≤ m) : LinearSeed m 8 := by
  apply BoundedRigid.residue_threshold (a := 7) (W := 38)
    (by decide) (by decide) rows8 rows8_mod rows8_max q8
    (fun i x hx => available8 x (rows8_allowed i (List.mem_toFinset.mpr hx))) m
    (by omega) hm

theorem linear8 (m : ℕ) (hm : 33 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 8 ∧ IsLinear H := LinearSeed.realize (bounded8 m hm)

theorem available9 : ∀ x ∈ increments9, LinearSeed (x + 1) 9 := by
  intro x hx
  fin_cases hx
  · exact q22
  · exact LinearSeed.restrict q26 (by decide) (by decide)
  · exact LinearSeed.restrict q33 (by decide) (by decide)
  · exact LinearSeed.restrict q34 (by decide) (by decide)
  · exact LinearSeed.restrict q38 (by decide) (by decide)
  · exact LinearSeed.restrict q39 (by decide) (by decide)
  · exact LinearSeed.restrict q44 (by decide) (by decide)
  · exact LinearSeed.restrict q46 (by decide) (by decide)
  · exact LinearSeed.restrict q51 (by decide) (by decide)
  · exact LinearSeed.restrict q52 (by decide) (by decide)
  · exact LinearSeed.restrict q57 (by decide) (by decide)
  · exact LinearSeed.restrict q58 (by decide) (by decide)
  · exact LinearSeed.restrict q62 (by decide) (by decide)
  · exact LinearSeed.restrict q66 (by decide) (by decide)
  · exact LinearSeed.restrict q69 (by decide) (by decide)
  · exact LinearSeed.restrict q74 (by decide) (by decide)
  · exact LinearSeed.restrict q77 (by decide) (by decide)
  · exact LinearSeed.restrict q82 (by decide) (by decide)

theorem bounded9 (m : ℕ) (hm : 62 ≤ m) : LinearSeed m 9 := by
  apply BoundedRigid.residue_threshold (a := 21) (W := 81)
    (by decide) (by decide) rows9 rows9_mod rows9_max q22
    (fun i x hx => available9 x (rows9_allowed i (List.mem_toFinset.mpr hx))) m
    (by omega) hm

theorem linear9 (m : ℕ) (hm : 62 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 9 ∧ IsLinear H := LinearSeed.realize (bounded9 m hm)

theorem available10 : ∀ x ∈ increments10, LinearSeed (x + 1) 10 := by
  intro x hx
  fin_cases hx
  · exact q26
  · exact q33
  · exact q34
  · exact LinearSeed.restrict q38 (by decide) (by decide)
  · exact LinearSeed.restrict q39 (by decide) (by decide)
  · exact q44
  · exact LinearSeed.restrict q46 (by decide) (by decide)
  · exact LinearSeed.restrict q52 (by decide) (by decide)
  · exact q55
  · exact LinearSeed.restrict q57 (by decide) (by decide)
  · exact LinearSeed.restrict q62 (by decide) (by decide)
  · exact LinearSeed.restrict q65 (by decide) (by decide)
  · exact q66
  · exact q68
  · exact q74
  · exact LinearSeed.restrict q78 (by decide) (by decide)
  · exact q85
  · exact q86

theorem bounded10 (m : ℕ) (hm : 74 ≤ m) : LinearSeed m 10 := by
  apply BoundedRigid.residue_threshold (a := 25) (W := 97)
    (by decide) (by decide) rows10 rows10_mod rows10_max q26
    (fun i x hx => available10 x (rows10_allowed i (List.mem_toFinset.mpr hx))) m
    (by omega) hm

theorem linear10 (m : ℕ) (hm : 74 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 10 ∧ IsLinear H := LinearSeed.realize (bounded10 m hm)

theorem available11 : ∀ x ∈ increments11, LinearSeed (x + 1) 11 := by
  intro x hx
  fin_cases hx
  · exact q38
  · exact LinearSeed.restrict q39 (by decide) (by decide)
  · exact LinearSeed.restrict q46 (by decide) (by decide)
  · exact LinearSeed.restrict q52 (by decide) (by decide)
  · exact LinearSeed.restrict q57 (by decide) (by decide)
  · exact LinearSeed.restrict q58 (by decide) (by decide)
  · exact LinearSeed.restrict q62 (by decide) (by decide)
  · exact LinearSeed.restrict q65 (by decide) (by decide)
  · exact LinearSeed.restrict q69 (by decide) (by decide)
  · exact LinearSeed.restrict q78 (by decide) (by decide)
  · exact LinearSeed.restrict q87 (by decide) (by decide)
  · exact LinearSeed.restrict q91 (by decide) (by decide)
  · exact LinearSeed.restrict q92 (by decide) (by decide)
  · exact LinearSeed.restrict q93 (by decide) (by decide)
  · exact LinearSeed.restrict q104 (by decide) (by decide)
  · exact LinearSeed.restrict q116 (by decide) (by decide)
  · exact LinearSeed.restrict q117 (by decide) (by decide)
  · exact LinearSeed.restrict q138 (by decide) (by decide)

theorem bounded11 (m : ℕ) (hm : 112 ≤ m) : LinearSeed m 11 := by
  apply BoundedRigid.residue_threshold (a := 37) (W := 147)
    (by decide) (by decide) rows11 rows11_mod rows11_max q38
    (fun i x hx => available11 x (rows11_allowed i (List.mem_toFinset.mpr hx))) m
    (by omega) hm

theorem linear11 (m : ℕ) (hm : 112 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 11 ∧ IsLinear H := LinearSeed.realize (bounded11 m hm)

theorem available12 : ∀ x ∈ increments12, LinearSeed (x + 1) 12 := by
  intro x hx
  fin_cases hx
  · exact q39
  · exact q46
  · exact q52
  · exact q57
  · exact q58
  · exact q62
  · exact q65
  · exact q69
  · exact q76
  · exact q78
  · exact q87
  · exact q91
  · exact q92
  · exact q93
  · exact q104
  · exact q117
  · exact q124
  · exact q143

theorem bounded12 (m : ℕ) (hm : 113 ≤ m) : LinearSeed m 12 := by
  apply BoundedRigid.residue_threshold (a := 38) (W := 149)
    (by decide) (by decide) rows12 rows12_mod rows12_max q39
    (fun i x hx => available12 x (rows12_allowed i (List.mem_toFinset.mpr hx))) m
    (by omega) hm

theorem linear12 (m : ℕ) (hm : 113 ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H 12 ∧ IsLinear H := LinearSeed.realize (bounded12 m hm)

def threshold : ℕ → ℕ
  | 8 => 33
  | 9 => 62
  | 10 => 74
  | 11 => 112
  | 12 => 113
  | _ => 0

/-- The exact five-entry threshold table, with standard simple hypergraphs,
standard perfect matchings, and the intersection definition of linearity. -/
theorem linear_thresholds (t m : ℕ) (ht : t ∈ ({8, 9, 10, 11, 12} : Finset ℕ))
    (hm : threshold t ≤ m) :
    ∃ H : Hypergraph (Fin 3 × Fin m), Uniform H 3 ∧ BalancedPartite H 3 m ∧
      IsRigid H t ∧ IsLinear H := by
  fin_cases ht
  · exact linear8 m (by simpa [threshold] using hm)
  · exact linear9 m (by simpa [threshold] using hm)
  · exact linear10 m (by simpa [threshold] using hm)
  · exact linear11 m (by simpa [threshold] using hm)
  · exact linear12 m (by simpa [threshold] using hm)

end RigidGHZ.Supplement.LinearThresholds
