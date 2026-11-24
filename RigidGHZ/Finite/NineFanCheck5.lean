module

public import RigidGHZ.Finite.NineFanCheck4

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
local instance nineFanDecidableCheck5 (F : NineFan) : Decidable F.Valid := by
  unfold NineFan.Valid Function.Injective
  infer_instance

theorem nineFan_valid_30 (i : Fin 21) : (nineFan ⟨30*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨30*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨30*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_31 (i : Fin 21) : (nineFan ⟨31*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨31*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨31*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_32 (i : Fin 21) : (nineFan ⟨32*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨32*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨32*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_33 (i : Fin 21) : (nineFan ⟨33*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨33*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨33*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_34 (i : Fin 21) : (nineFan ⟨34*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨34*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨34*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineFan_valid_35 (i : Fin 21) : (nineFan ⟨35*21+i.val, by omega⟩).Valid := by
  have hc : (List.finRange 21).all (fun i => decide (nineFan ⟨35*21+i.val, by omega⟩).Valid) = true := by decide +kernel
  have h : ∀ i : Fin 21, (nineFan ⟨35*21+i.val, by omega⟩).Valid := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i


end RigidGHZ.Finite
