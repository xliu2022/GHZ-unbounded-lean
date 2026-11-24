module

public import RigidGHZ.Finite.NineFanCheck0

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
local instance nineFanDecidableCheck1 (F : NineFan) : Decidable F.Valid := by
  unfold NineFan.Valid Function.Injective
  infer_instance

theorem nineFan_valid_6 (i : Fin 21) : (nineFan ⟨6*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨6*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨6*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_7 (i : Fin 21) : (nineFan ⟨7*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨7*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨7*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_8 (i : Fin 21) : (nineFan ⟨8*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨8*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨8*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_9 (i : Fin 21) : (nineFan ⟨9*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨9*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨9*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_10 (i : Fin 21) : (nineFan ⟨10*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨10*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨10*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_11 (i : Fin 21) : (nineFan ⟨11*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨11*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨11*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i


end RigidGHZ.Finite
