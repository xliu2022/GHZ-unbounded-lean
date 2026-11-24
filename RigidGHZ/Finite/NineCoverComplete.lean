module
public import RigidGHZ.Finite.NineCoverSound
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option Elab.async false
local instance coverCompleteDecidable (i : Fin 280) : Decidable (NineCoverComplete i) := by
  unfold NineCoverComplete
  infer_instance

theorem nineCover_complete_0 (i : Fin 28) : NineCoverComplete ⟨0*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨0*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨0*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_1 (i : Fin 28) : NineCoverComplete ⟨1*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨1*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨1*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_2 (i : Fin 28) : NineCoverComplete ⟨2*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨2*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨2*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_3 (i : Fin 28) : NineCoverComplete ⟨3*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨3*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨3*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_4 (i : Fin 28) : NineCoverComplete ⟨4*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨4*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨4*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_5 (i : Fin 28) : NineCoverComplete ⟨5*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨5*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨5*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_6 (i : Fin 28) : NineCoverComplete ⟨6*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨6*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨6*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_7 (i : Fin 28) : NineCoverComplete ⟨7*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨7*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨7*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_8 (i : Fin 28) : NineCoverComplete ⟨8*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨8*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨8*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete_9 (i : Fin 28) : NineCoverComplete ⟨9*28+i.val,by omega⟩ := by
  have hc : (List.finRange 28).all (fun i => decide (NineCoverComplete ⟨9*28+i.val,by omega⟩)) = true := by decide +kernel
  have h : ∀ i : Fin 28, NineCoverComplete ⟨9*28+i.val,by omega⟩ := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact h i

theorem nineCover_complete (i : Fin 280) : NineCoverComplete i := by
  have h : ∀ j : Fin 10, ∀ r : Fin 28, NineCoverComplete ⟨j.val*28+r.val,by omega⟩ := by
    intro j
    fin_cases j
    · exact nineCover_complete_0
    · exact nineCover_complete_1
    · exact nineCover_complete_2
    · exact nineCover_complete_3
    · exact nineCover_complete_4
    · exact nineCover_complete_5
    · exact nineCover_complete_6
    · exact nineCover_complete_7
    · exact nineCover_complete_8
    · exact nineCover_complete_9
  let j : Fin 10 := ⟨i.val/28,by omega⟩
  let r : Fin 28 := ⟨i.val%28,Nat.mod_lt _ (by decide)⟩
  have hi : (⟨j.val*28+r.val,by omega⟩ : Fin 280) = i := by
    apply Fin.ext
    dsimp [j,r]
    omega
  simpa only [hi] using h j r

end RigidGHZ.Finite
