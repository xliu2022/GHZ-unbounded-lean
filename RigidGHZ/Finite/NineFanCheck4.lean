module

public import RigidGHZ.Finite.NineFanCheck3

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
local instance nineFanDecidableCheck4 (F : NineFan) : Decidable F.Valid := by
  unfold NineFan.Valid Function.Injective
  infer_instance

theorem nineFan_valid_24 (i : Fin 21) : (nineFan ⟨24*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨24*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨24*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_25 (i : Fin 21) : (nineFan ⟨25*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨25*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨25*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_26 (i : Fin 21) : (nineFan ⟨26*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨26*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨26*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_27 (i : Fin 21) : (nineFan ⟨27*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨27*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨27*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_28 (i : Fin 21) : (nineFan ⟨28*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨28*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨28*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_29 (i : Fin 21) : (nineFan ⟨29*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨29*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨29*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i


end RigidGHZ.Finite
