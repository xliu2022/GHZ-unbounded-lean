module

public import RigidGHZ.Finite.NineConflictCheck0
public import RigidGHZ.Finite.NineConflictCheck1
public import RigidGHZ.Finite.NineConflictCheck2
public import RigidGHZ.Finite.NineConflictCheck3
public import RigidGHZ.Finite.NineConflictCheck4
public import RigidGHZ.Finite.NineConflictCheck5
public import RigidGHZ.Finite.NineConflictCheck6
public import RigidGHZ.Finite.NineConflictCheck7
public import RigidGHZ.Finite.NineConflictCheck8
public import RigidGHZ.Finite.NineConflictCheck9
public import RigidGHZ.Finite.NineConflictCheck10
public import RigidGHZ.Finite.NineConflictCheck11

@[expose] public section
namespace RigidGHZ.Finite

 theorem nineConflict_code_valid (e : Fin 84) (k : Fin 45) : nineConflictCodeValid e k := by
  fin_cases e
  · exact nineConflict_valid_0 k
  · exact nineConflict_valid_1 k
  · exact nineConflict_valid_2 k
  · exact nineConflict_valid_3 k
  · exact nineConflict_valid_4 k
  · exact nineConflict_valid_5 k
  · exact nineConflict_valid_6 k
  · exact nineConflict_valid_7 k
  · exact nineConflict_valid_8 k
  · exact nineConflict_valid_9 k
  · exact nineConflict_valid_10 k
  · exact nineConflict_valid_11 k
  · exact nineConflict_valid_12 k
  · exact nineConflict_valid_13 k
  · exact nineConflict_valid_14 k
  · exact nineConflict_valid_15 k
  · exact nineConflict_valid_16 k
  · exact nineConflict_valid_17 k
  · exact nineConflict_valid_18 k
  · exact nineConflict_valid_19 k
  · exact nineConflict_valid_20 k
  · exact nineConflict_valid_21 k
  · exact nineConflict_valid_22 k
  · exact nineConflict_valid_23 k
  · exact nineConflict_valid_24 k
  · exact nineConflict_valid_25 k
  · exact nineConflict_valid_26 k
  · exact nineConflict_valid_27 k
  · exact nineConflict_valid_28 k
  · exact nineConflict_valid_29 k
  · exact nineConflict_valid_30 k
  · exact nineConflict_valid_31 k
  · exact nineConflict_valid_32 k
  · exact nineConflict_valid_33 k
  · exact nineConflict_valid_34 k
  · exact nineConflict_valid_35 k
  · exact nineConflict_valid_36 k
  · exact nineConflict_valid_37 k
  · exact nineConflict_valid_38 k
  · exact nineConflict_valid_39 k
  · exact nineConflict_valid_40 k
  · exact nineConflict_valid_41 k
  · exact nineConflict_valid_42 k
  · exact nineConflict_valid_43 k
  · exact nineConflict_valid_44 k
  · exact nineConflict_valid_45 k
  · exact nineConflict_valid_46 k
  · exact nineConflict_valid_47 k
  · exact nineConflict_valid_48 k
  · exact nineConflict_valid_49 k
  · exact nineConflict_valid_50 k
  · exact nineConflict_valid_51 k
  · exact nineConflict_valid_52 k
  · exact nineConflict_valid_53 k
  · exact nineConflict_valid_54 k
  · exact nineConflict_valid_55 k
  · exact nineConflict_valid_56 k
  · exact nineConflict_valid_57 k
  · exact nineConflict_valid_58 k
  · exact nineConflict_valid_59 k
  · exact nineConflict_valid_60 k
  · exact nineConflict_valid_61 k
  · exact nineConflict_valid_62 k
  · exact nineConflict_valid_63 k
  · exact nineConflict_valid_64 k
  · exact nineConflict_valid_65 k
  · exact nineConflict_valid_66 k
  · exact nineConflict_valid_67 k
  · exact nineConflict_valid_68 k
  · exact nineConflict_valid_69 k
  · exact nineConflict_valid_70 k
  · exact nineConflict_valid_71 k
  · exact nineConflict_valid_72 k
  · exact nineConflict_valid_73 k
  · exact nineConflict_valid_74 k
  · exact nineConflict_valid_75 k
  · exact nineConflict_valid_76 k
  · exact nineConflict_valid_77 k
  · exact nineConflict_valid_78 k
  · exact nineConflict_valid_79 k
  · exact nineConflict_valid_80 k
  · exact nineConflict_valid_81 k
  · exact nineConflict_valid_82 k
  · exact nineConflict_valid_83 k

theorem ninePartitionCode_mem (e : Fin 84) (i : Fin 280) :
    nineEdge e ∈ ninePartition i ↔ nineCodeMem e (ninePartitionCode i) := by
  simp [ninePartition,nineCodeMem,nineEdge_injective.eq_iff]

theorem nineConflict_valid (e : Fin 84) (k : Fin 45) :
    let c := nineConflict e k
    nineEdge e ∈ ninePartition c.1 ∧ nineEdge e ∈ ninePartition c.2 ∧
      ninePartition c.1 ≠ ninePartition c.2 := by
  obtain ⟨he1,he2,hnot⟩ := nineConflict_code_valid e k
  refine ⟨(ninePartitionCode_mem e _).mpr he1,(ninePartitionCode_mem e _).mpr he2,?_⟩
  intro heq
  have hsub : ∀ x, nineCodeMem x (ninePartitionCode (nineConflict e k).1) →
      nineCodeMem x (ninePartitionCode (nineConflict e k).2) := by
    intro x hx
    apply (ninePartitionCode_mem x _).mp
    rw [←heq]
    exact (ninePartitionCode_mem x _).mpr hx
  apply hnot
  exact ⟨hsub _ (Or.inl rfl),hsub _ (Or.inr (Or.inl rfl)),hsub _ (Or.inr (Or.inr rfl))⟩


end RigidGHZ.Finite
