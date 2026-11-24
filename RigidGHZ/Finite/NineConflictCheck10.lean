module

public import RigidGHZ.Finite.NineConflictCheck9

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck10 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck10 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_70 (k : Fin 45) : nineConflictCodeValid 70 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 70 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 70 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_71 (k : Fin 45) : nineConflictCodeValid 71 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 71 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 71 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_72 (k : Fin 45) : nineConflictCodeValid 72 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 72 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 72 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_73 (k : Fin 45) : nineConflictCodeValid 73 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 73 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 73 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_74 (k : Fin 45) : nineConflictCodeValid 74 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 74 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 74 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_75 (k : Fin 45) : nineConflictCodeValid 75 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 75 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 75 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_76 (k : Fin 45) : nineConflictCodeValid 76 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 76 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 76 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
