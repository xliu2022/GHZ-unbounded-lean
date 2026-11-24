module

public import RigidGHZ.Finite.NineConflictCheck0

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck1 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck1 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_7 (k : Fin 45) : nineConflictCodeValid 7 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 7 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 7 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_8 (k : Fin 45) : nineConflictCodeValid 8 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 8 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 8 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_9 (k : Fin 45) : nineConflictCodeValid 9 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 9 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 9 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_10 (k : Fin 45) : nineConflictCodeValid 10 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 10 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 10 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_11 (k : Fin 45) : nineConflictCodeValid 11 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 11 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 11 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_12 (k : Fin 45) : nineConflictCodeValid 12 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 12 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 12 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_13 (k : Fin 45) : nineConflictCodeValid 13 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 13 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 13 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
