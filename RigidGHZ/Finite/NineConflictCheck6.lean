module

public import RigidGHZ.Finite.NineConflictCheck5

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck6 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck6 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_42 (k : Fin 45) : nineConflictCodeValid 42 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 42 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 42 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_43 (k : Fin 45) : nineConflictCodeValid 43 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 43 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 43 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_44 (k : Fin 45) : nineConflictCodeValid 44 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 44 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 44 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_45 (k : Fin 45) : nineConflictCodeValid 45 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 45 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 45 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_46 (k : Fin 45) : nineConflictCodeValid 46 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 46 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 46 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_47 (k : Fin 45) : nineConflictCodeValid 47 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 47 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 47 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_48 (k : Fin 45) : nineConflictCodeValid 48 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 48 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 48 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
