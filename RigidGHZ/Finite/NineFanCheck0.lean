module

public import RigidGHZ.Finite.NineFanData

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
local instance nineFanDecidableCheck0 (F : NineFan) : Decidable F.Valid := by
  unfold NineFan.Valid Function.Injective
  infer_instance

theorem nineFan_valid_0 (i : Fin 21) : (nineFan ⟨0*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨0*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨0*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_1 (i : Fin 21) : (nineFan ⟨1*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨1*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨1*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_2 (i : Fin 21) : (nineFan ⟨2*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨2*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨2*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_3 (i : Fin 21) : (nineFan ⟨3*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨3*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨3*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_4 (i : Fin 21) : (nineFan ⟨4*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨4*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨4*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_5 (i : Fin 21) : (nineFan ⟨5*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨5*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨5*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i


end RigidGHZ.Finite
