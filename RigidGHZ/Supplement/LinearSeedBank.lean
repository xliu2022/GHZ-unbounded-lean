module

public import RigidGHZ.Supplement.LinearSeeds.Latin
public import RigidGHZ.Supplement.LinearSeeds.A5
public import RigidGHZ.Supplement.LinearSeeds.A7
public import RigidGHZ.Supplement.LinearSeeds.A11
public import RigidGHZ.Supplement.LinearSeeds.A13
public import RigidGHZ.Supplement.LinearSeeds.A17
public import RigidGHZ.Supplement.LinearSeeds.A19
public import RigidGHZ.Supplement.LinearSeeds.A23
public import RigidGHZ.Supplement.LinearSeeds.A29
public import RigidGHZ.Supplement.LinearSeeds.A31
public import RigidGHZ.Supplement.LinearSeeds.A37
public import RigidGHZ.Supplement.LinearSeeds.A41
public import RigidGHZ.Supplement.LinearSeeds.A43

/-! All forty actual linear rigid seeds in the supplementary residue table. -/

@[expose] public section

namespace RigidGHZ.Supplement.LinearSeeds

/-- The part size and number of retained matchings in each printed bank row. -/
def bank : Finset (ℕ × ℕ) :=
  {(8, 8), (20, 8), (21, 8), (22, 9), (24, 8), (26, 10), (30, 8),
   (33, 10), (34, 10), (38, 11), (39, 12), (44, 10), (46, 12), (51, 10),
   (52, 12), (55, 10), (57, 12), (58, 12), (62, 12), (65, 12), (66, 10),
   (68, 10), (69, 12), (74, 10), (76, 12), (77, 10), (78, 12), (82, 10),
   (85, 10), (86, 10), (87, 12), (91, 12), (92, 12), (93, 12), (104, 12),
   (116, 12), (117, 12), (124, 12), (138, 12), (143, 12)}

theorem bank_card : bank.card = 40 := by decide

/-- Every row is realized by a genuine balanced linear rigid hypergraph. -/
theorem bank_correct (row : ℕ × ℕ) (hrow : row ∈ bank) :
    LinearSeed row.1 row.2 := by
  fin_cases hrow
  · exact q8
  · exact q20
  · exact q21
  · exact q22
  · exact q24
  · exact q26
  · exact q30
  · exact q33
  · exact q34
  · exact q38
  · exact q39
  · exact q44
  · exact q46
  · exact q51
  · exact q52
  · exact q55
  · exact q57
  · exact q58
  · exact q62
  · exact q65
  · exact q66
  · exact q68
  · exact q69
  · exact q74
  · exact q76
  · exact q77
  · exact q78
  · exact q82
  · exact q85
  · exact q86
  · exact q87
  · exact q91
  · exact q92
  · exact q93
  · exact q104
  · exact q116
  · exact q117
  · exact q124
  · exact q138
  · exact q143

theorem bank_realized (q d : ℕ) (hrow : (q, d) ∈ bank) :
    ∃ H : Hypergraph (Fin 3 × Fin q), Uniform H 3 ∧ BalancedPartite H 3 q ∧
      IsRigid H d ∧ IsLinear H :=
  LinearSeed.realize (bank_correct (q, d) hrow)

end RigidGHZ.Supplement.LinearSeeds
