module

public import RigidGHZ.Finite.NineConflictCheck10

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck11 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck11 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_77 (k : Fin 45) : nineConflictCodeValid 77 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 77 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 77 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_78 (k : Fin 45) : nineConflictCodeValid 78 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 78 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 78 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_79 (k : Fin 45) : nineConflictCodeValid 79 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 79 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 79 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_80 (k : Fin 45) : nineConflictCodeValid 80 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 80 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 80 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_81 (k : Fin 45) : nineConflictCodeValid 81 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 81 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 81 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_82 (k : Fin 45) : nineConflictCodeValid 82 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 82 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 82 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_83 (k : Fin 45) : nineConflictCodeValid 83 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 83 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 83 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
