module

public import RigidGHZ.Finite.NineConflictCheck8

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

local instance nineCodeMemDecidableCheck9 (e : Fin 84) (c : Fin 84 × Fin 84 × Fin 84) : Decidable (nineCodeMem e c) := by
  unfold nineCodeMem
  infer_instance
local instance nineConflictCodeDecidableCheck9 (e : Fin 84) (k : Fin 45) : Decidable (nineConflictCodeValid e k) := by
  unfold nineConflictCodeValid
  infer_instance

 theorem nineConflict_valid_63 (k : Fin 45) : nineConflictCodeValid 63 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 63 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 63 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_64 (k : Fin 45) : nineConflictCodeValid 64 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 64 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 64 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_65 (k : Fin 45) : nineConflictCodeValid 65 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 65 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 65 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_66 (k : Fin 45) : nineConflictCodeValid 66 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 66 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 66 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_67 (k : Fin 45) : nineConflictCodeValid 67 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 67 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 67 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_68 (k : Fin 45) : nineConflictCodeValid 68 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 68 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 68 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k

 theorem nineConflict_valid_69 (k : Fin 45) : nineConflictCodeValid 69 k := by
  have h : (List.finRange 45).all (fun k => decide (nineConflictCodeValid 69 k)) = true := by decide +kernel
  have hh : ∀ k : Fin 45, nineConflictCodeValid 69 k := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using h
  exact hh k


end RigidGHZ.Finite
