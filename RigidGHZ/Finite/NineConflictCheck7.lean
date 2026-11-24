module

public import RigidGHZ.Finite.NineConflictCheck6

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck7 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck7 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_49 (k : Fin 45) : nineConflictCodeValid 49 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 49 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 49 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_50 (k : Fin 45) : nineConflictCodeValid 50 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 50 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 50 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_51 (k : Fin 45) : nineConflictCodeValid 51 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 51 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 51 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_52 (k : Fin 45) : nineConflictCodeValid 52 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 52 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 52 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_53 (k : Fin 45) : nineConflictCodeValid 53 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 53 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 53 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_54 (k : Fin 45) : nineConflictCodeValid 54 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 54 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 54 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_55 (k : Fin 45) : nineConflictCodeValid 55 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 55 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 55 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
