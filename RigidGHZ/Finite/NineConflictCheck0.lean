module

public import RigidGHZ.Finite.NineConflictData

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck0 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck0 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_0 (k : Fin 45) : nineConflictCodeValid 0 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 0 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 0 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_1 (k : Fin 45) : nineConflictCodeValid 1 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 1 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 1 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_2 (k : Fin 45) : nineConflictCodeValid 2 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 2 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 2 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_3 (k : Fin 45) : nineConflictCodeValid 3 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 3 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 3 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_4 (k : Fin 45) : nineConflictCodeValid 4 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 4 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 4 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_5 (k : Fin 45) : nineConflictCodeValid 5 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 5 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 5 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_6 (k : Fin 45) : nineConflictCodeValid 6 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 6 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 6 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
