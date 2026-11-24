module

public import RigidGHZ.Finite.NineConflictCheck2

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck3 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck3 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_21 (k : Fin 45) : nineConflictCodeValid 21 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 21 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 21 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_22 (k : Fin 45) : nineConflictCodeValid 22 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 22 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 22 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_23 (k : Fin 45) : nineConflictCodeValid 23 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 23 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 23 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_24 (k : Fin 45) : nineConflictCodeValid 24 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 24 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 24 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_25 (k : Fin 45) : nineConflictCodeValid 25 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 25 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 25 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_26 (k : Fin 45) : nineConflictCodeValid 26 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 26 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 26 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_27 (k : Fin 45) : nineConflictCodeValid 27 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 27 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 27 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
