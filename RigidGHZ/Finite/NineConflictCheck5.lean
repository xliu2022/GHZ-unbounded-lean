module

public import RigidGHZ.Finite.NineConflictCheck4

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck5 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck5 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_35 (k : Fin 45) : nineConflictCodeValid 35 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 35 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 35 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_36 (k : Fin 45) : nineConflictCodeValid 36 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 36 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 36 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_37 (k : Fin 45) : nineConflictCodeValid 37 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 37 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 37 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_38 (k : Fin 45) : nineConflictCodeValid 38 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 38 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 38 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_39 (k : Fin 45) : nineConflictCodeValid 39 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 39 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 39 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_40 (k : Fin 45) : nineConflictCodeValid 40 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 40 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 40 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_41 (k : Fin 45) : nineConflictCodeValid 41 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 41 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 41 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
