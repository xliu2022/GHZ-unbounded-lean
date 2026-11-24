module

public import RigidGHZ.Finite.NineConflictCheck3

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck4 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck4 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_28 (k : Fin 45) : nineConflictCodeValid 28 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 28 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 28 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_29 (k : Fin 45) : nineConflictCodeValid 29 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 29 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 29 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_30 (k : Fin 45) : nineConflictCodeValid 30 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 30 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 30 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_31 (k : Fin 45) : nineConflictCodeValid 31 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 31 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 31 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_32 (k : Fin 45) : nineConflictCodeValid 32 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 32 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 32 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_33 (k : Fin 45) : nineConflictCodeValid 33 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 33 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 33 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_34 (k : Fin 45) : nineConflictCodeValid 34 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 34 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 34 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
