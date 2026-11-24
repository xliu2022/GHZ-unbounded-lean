module

public import RigidGHZ.Finite.NineConflictCheck7

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck8 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck8 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_56 (k : Fin 45) : nineConflictCodeValid 56 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 56 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 56 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_57 (k : Fin 45) : nineConflictCodeValid 57 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 57 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 57 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_58 (k : Fin 45) : nineConflictCodeValid 58 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 58 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 58 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_59 (k : Fin 45) : nineConflictCodeValid 59 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 59 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 59 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_60 (k : Fin 45) : nineConflictCodeValid 60 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 60 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 60 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_61 (k : Fin 45) : nineConflictCodeValid 61 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 61 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 61 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_62 (k : Fin 45) : nineConflictCodeValid 62 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 62 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 62 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
