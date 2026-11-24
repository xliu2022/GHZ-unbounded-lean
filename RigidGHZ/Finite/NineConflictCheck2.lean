module

public import RigidGHZ.Finite.NineConflictCheck1

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck2 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck2 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_14 (k : Fin 45) : nineConflictCodeValid 14 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 14 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 14 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_15 (k : Fin 45) : nineConflictCodeValid 15 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 15 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 15 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_16 (k : Fin 45) : nineConflictCodeValid 16 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 16 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 16 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_17 (k : Fin 45) : nineConflictCodeValid 17 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 17 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 17 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_18 (k : Fin 45) : nineConflictCodeValid 18 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 18 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 18 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_19 (k : Fin 45) : nineConflictCodeValid 19 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 19 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 19 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_20 (k : Fin 45) : nineConflictCodeValid 20 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 20 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 20 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
