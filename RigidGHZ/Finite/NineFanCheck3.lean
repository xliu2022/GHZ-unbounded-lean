module

public import RigidGHZ.Finite.NineFanCheck2

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
local instance nineFanDecidableCheck3 (F : NineFan) : Decidable F.Valid := by
  unfold NineFan.Valid Function.Injective
  infer_instance

theorem nineFan_valid_18 (i : Fin 21) : (nineFan ⟨18*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨18*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨18*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_19 (i : Fin 21) : (nineFan ⟨19*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨19*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨19*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_20 (i : Fin 21) : (nineFan ⟨20*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨20*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨20*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_21 (i : Fin 21) : (nineFan ⟨21*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨21*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨21*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_22 (i : Fin 21) : (nineFan ⟨22*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨22*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨22*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_23 (i : Fin 21) : (nineFan ⟨23*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨23*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨23*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i


end RigidGHZ.Finite
