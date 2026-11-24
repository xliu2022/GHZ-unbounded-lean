module
public import RigidGHZ.Finite.NineCoverData
@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000
set_option Elab.async false
local instance coverSoundDecidable (e : Fin 84) (p : Fin 84 × Fin 84 × Fin 84) :
    Decidable (nineCodeMem e p) := by unfold nineCodeMem; infer_instance

theorem nineCover_sound_0 (i : Fin 280) (hi : i ∈ nineCoverIndices 0) :
    nineCodeMem 0 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 0).all (fun i => decide (nineCodeMem 0 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 0, nineCodeMem 0 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_1 (i : Fin 280) (hi : i ∈ nineCoverIndices 1) :
    nineCodeMem 1 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 1).all (fun i => decide (nineCodeMem 1 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 1, nineCodeMem 1 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_2 (i : Fin 280) (hi : i ∈ nineCoverIndices 2) :
    nineCodeMem 2 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 2).all (fun i => decide (nineCodeMem 2 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 2, nineCodeMem 2 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_3 (i : Fin 280) (hi : i ∈ nineCoverIndices 3) :
    nineCodeMem 3 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 3).all (fun i => decide (nineCodeMem 3 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 3, nineCodeMem 3 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_4 (i : Fin 280) (hi : i ∈ nineCoverIndices 4) :
    nineCodeMem 4 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 4).all (fun i => decide (nineCodeMem 4 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 4, nineCodeMem 4 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_5 (i : Fin 280) (hi : i ∈ nineCoverIndices 5) :
    nineCodeMem 5 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 5).all (fun i => decide (nineCodeMem 5 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 5, nineCodeMem 5 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_6 (i : Fin 280) (hi : i ∈ nineCoverIndices 6) :
    nineCodeMem 6 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 6).all (fun i => decide (nineCodeMem 6 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 6, nineCodeMem 6 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_7 (i : Fin 280) (hi : i ∈ nineCoverIndices 7) :
    nineCodeMem 7 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 7).all (fun i => decide (nineCodeMem 7 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 7, nineCodeMem 7 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_8 (i : Fin 280) (hi : i ∈ nineCoverIndices 8) :
    nineCodeMem 8 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 8).all (fun i => decide (nineCodeMem 8 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 8, nineCodeMem 8 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_9 (i : Fin 280) (hi : i ∈ nineCoverIndices 9) :
    nineCodeMem 9 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 9).all (fun i => decide (nineCodeMem 9 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 9, nineCodeMem 9 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_10 (i : Fin 280) (hi : i ∈ nineCoverIndices 10) :
    nineCodeMem 10 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 10).all (fun i => decide (nineCodeMem 10 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 10, nineCodeMem 10 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_11 (i : Fin 280) (hi : i ∈ nineCoverIndices 11) :
    nineCodeMem 11 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 11).all (fun i => decide (nineCodeMem 11 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 11, nineCodeMem 11 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_12 (i : Fin 280) (hi : i ∈ nineCoverIndices 12) :
    nineCodeMem 12 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 12).all (fun i => decide (nineCodeMem 12 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 12, nineCodeMem 12 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_13 (i : Fin 280) (hi : i ∈ nineCoverIndices 13) :
    nineCodeMem 13 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 13).all (fun i => decide (nineCodeMem 13 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 13, nineCodeMem 13 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_14 (i : Fin 280) (hi : i ∈ nineCoverIndices 14) :
    nineCodeMem 14 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 14).all (fun i => decide (nineCodeMem 14 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 14, nineCodeMem 14 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_15 (i : Fin 280) (hi : i ∈ nineCoverIndices 15) :
    nineCodeMem 15 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 15).all (fun i => decide (nineCodeMem 15 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 15, nineCodeMem 15 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_16 (i : Fin 280) (hi : i ∈ nineCoverIndices 16) :
    nineCodeMem 16 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 16).all (fun i => decide (nineCodeMem 16 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 16, nineCodeMem 16 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_17 (i : Fin 280) (hi : i ∈ nineCoverIndices 17) :
    nineCodeMem 17 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 17).all (fun i => decide (nineCodeMem 17 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 17, nineCodeMem 17 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_18 (i : Fin 280) (hi : i ∈ nineCoverIndices 18) :
    nineCodeMem 18 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 18).all (fun i => decide (nineCodeMem 18 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 18, nineCodeMem 18 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_19 (i : Fin 280) (hi : i ∈ nineCoverIndices 19) :
    nineCodeMem 19 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 19).all (fun i => decide (nineCodeMem 19 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 19, nineCodeMem 19 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_20 (i : Fin 280) (hi : i ∈ nineCoverIndices 20) :
    nineCodeMem 20 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 20).all (fun i => decide (nineCodeMem 20 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 20, nineCodeMem 20 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_21 (i : Fin 280) (hi : i ∈ nineCoverIndices 21) :
    nineCodeMem 21 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 21).all (fun i => decide (nineCodeMem 21 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 21, nineCodeMem 21 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_22 (i : Fin 280) (hi : i ∈ nineCoverIndices 22) :
    nineCodeMem 22 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 22).all (fun i => decide (nineCodeMem 22 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 22, nineCodeMem 22 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_23 (i : Fin 280) (hi : i ∈ nineCoverIndices 23) :
    nineCodeMem 23 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 23).all (fun i => decide (nineCodeMem 23 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 23, nineCodeMem 23 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_24 (i : Fin 280) (hi : i ∈ nineCoverIndices 24) :
    nineCodeMem 24 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 24).all (fun i => decide (nineCodeMem 24 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 24, nineCodeMem 24 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_25 (i : Fin 280) (hi : i ∈ nineCoverIndices 25) :
    nineCodeMem 25 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 25).all (fun i => decide (nineCodeMem 25 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 25, nineCodeMem 25 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_26 (i : Fin 280) (hi : i ∈ nineCoverIndices 26) :
    nineCodeMem 26 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 26).all (fun i => decide (nineCodeMem 26 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 26, nineCodeMem 26 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_27 (i : Fin 280) (hi : i ∈ nineCoverIndices 27) :
    nineCodeMem 27 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 27).all (fun i => decide (nineCodeMem 27 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 27, nineCodeMem 27 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_28 (i : Fin 280) (hi : i ∈ nineCoverIndices 28) :
    nineCodeMem 28 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 28).all (fun i => decide (nineCodeMem 28 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 28, nineCodeMem 28 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_29 (i : Fin 280) (hi : i ∈ nineCoverIndices 29) :
    nineCodeMem 29 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 29).all (fun i => decide (nineCodeMem 29 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 29, nineCodeMem 29 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_30 (i : Fin 280) (hi : i ∈ nineCoverIndices 30) :
    nineCodeMem 30 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 30).all (fun i => decide (nineCodeMem 30 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 30, nineCodeMem 30 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_31 (i : Fin 280) (hi : i ∈ nineCoverIndices 31) :
    nineCodeMem 31 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 31).all (fun i => decide (nineCodeMem 31 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 31, nineCodeMem 31 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_32 (i : Fin 280) (hi : i ∈ nineCoverIndices 32) :
    nineCodeMem 32 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 32).all (fun i => decide (nineCodeMem 32 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 32, nineCodeMem 32 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_33 (i : Fin 280) (hi : i ∈ nineCoverIndices 33) :
    nineCodeMem 33 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 33).all (fun i => decide (nineCodeMem 33 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 33, nineCodeMem 33 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_34 (i : Fin 280) (hi : i ∈ nineCoverIndices 34) :
    nineCodeMem 34 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 34).all (fun i => decide (nineCodeMem 34 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 34, nineCodeMem 34 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_35 (i : Fin 280) (hi : i ∈ nineCoverIndices 35) :
    nineCodeMem 35 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 35).all (fun i => decide (nineCodeMem 35 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 35, nineCodeMem 35 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_36 (i : Fin 280) (hi : i ∈ nineCoverIndices 36) :
    nineCodeMem 36 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 36).all (fun i => decide (nineCodeMem 36 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 36, nineCodeMem 36 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_37 (i : Fin 280) (hi : i ∈ nineCoverIndices 37) :
    nineCodeMem 37 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 37).all (fun i => decide (nineCodeMem 37 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 37, nineCodeMem 37 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_38 (i : Fin 280) (hi : i ∈ nineCoverIndices 38) :
    nineCodeMem 38 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 38).all (fun i => decide (nineCodeMem 38 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 38, nineCodeMem 38 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_39 (i : Fin 280) (hi : i ∈ nineCoverIndices 39) :
    nineCodeMem 39 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 39).all (fun i => decide (nineCodeMem 39 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 39, nineCodeMem 39 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_40 (i : Fin 280) (hi : i ∈ nineCoverIndices 40) :
    nineCodeMem 40 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 40).all (fun i => decide (nineCodeMem 40 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 40, nineCodeMem 40 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_41 (i : Fin 280) (hi : i ∈ nineCoverIndices 41) :
    nineCodeMem 41 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 41).all (fun i => decide (nineCodeMem 41 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 41, nineCodeMem 41 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_42 (i : Fin 280) (hi : i ∈ nineCoverIndices 42) :
    nineCodeMem 42 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 42).all (fun i => decide (nineCodeMem 42 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 42, nineCodeMem 42 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_43 (i : Fin 280) (hi : i ∈ nineCoverIndices 43) :
    nineCodeMem 43 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 43).all (fun i => decide (nineCodeMem 43 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 43, nineCodeMem 43 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_44 (i : Fin 280) (hi : i ∈ nineCoverIndices 44) :
    nineCodeMem 44 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 44).all (fun i => decide (nineCodeMem 44 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 44, nineCodeMem 44 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_45 (i : Fin 280) (hi : i ∈ nineCoverIndices 45) :
    nineCodeMem 45 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 45).all (fun i => decide (nineCodeMem 45 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 45, nineCodeMem 45 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_46 (i : Fin 280) (hi : i ∈ nineCoverIndices 46) :
    nineCodeMem 46 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 46).all (fun i => decide (nineCodeMem 46 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 46, nineCodeMem 46 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_47 (i : Fin 280) (hi : i ∈ nineCoverIndices 47) :
    nineCodeMem 47 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 47).all (fun i => decide (nineCodeMem 47 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 47, nineCodeMem 47 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_48 (i : Fin 280) (hi : i ∈ nineCoverIndices 48) :
    nineCodeMem 48 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 48).all (fun i => decide (nineCodeMem 48 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 48, nineCodeMem 48 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_49 (i : Fin 280) (hi : i ∈ nineCoverIndices 49) :
    nineCodeMem 49 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 49).all (fun i => decide (nineCodeMem 49 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 49, nineCodeMem 49 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_50 (i : Fin 280) (hi : i ∈ nineCoverIndices 50) :
    nineCodeMem 50 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 50).all (fun i => decide (nineCodeMem 50 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 50, nineCodeMem 50 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_51 (i : Fin 280) (hi : i ∈ nineCoverIndices 51) :
    nineCodeMem 51 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 51).all (fun i => decide (nineCodeMem 51 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 51, nineCodeMem 51 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_52 (i : Fin 280) (hi : i ∈ nineCoverIndices 52) :
    nineCodeMem 52 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 52).all (fun i => decide (nineCodeMem 52 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 52, nineCodeMem 52 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_53 (i : Fin 280) (hi : i ∈ nineCoverIndices 53) :
    nineCodeMem 53 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 53).all (fun i => decide (nineCodeMem 53 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 53, nineCodeMem 53 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_54 (i : Fin 280) (hi : i ∈ nineCoverIndices 54) :
    nineCodeMem 54 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 54).all (fun i => decide (nineCodeMem 54 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 54, nineCodeMem 54 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_55 (i : Fin 280) (hi : i ∈ nineCoverIndices 55) :
    nineCodeMem 55 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 55).all (fun i => decide (nineCodeMem 55 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 55, nineCodeMem 55 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_56 (i : Fin 280) (hi : i ∈ nineCoverIndices 56) :
    nineCodeMem 56 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 56).all (fun i => decide (nineCodeMem 56 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 56, nineCodeMem 56 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_57 (i : Fin 280) (hi : i ∈ nineCoverIndices 57) :
    nineCodeMem 57 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 57).all (fun i => decide (nineCodeMem 57 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 57, nineCodeMem 57 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_58 (i : Fin 280) (hi : i ∈ nineCoverIndices 58) :
    nineCodeMem 58 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 58).all (fun i => decide (nineCodeMem 58 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 58, nineCodeMem 58 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_59 (i : Fin 280) (hi : i ∈ nineCoverIndices 59) :
    nineCodeMem 59 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 59).all (fun i => decide (nineCodeMem 59 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 59, nineCodeMem 59 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_60 (i : Fin 280) (hi : i ∈ nineCoverIndices 60) :
    nineCodeMem 60 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 60).all (fun i => decide (nineCodeMem 60 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 60, nineCodeMem 60 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_61 (i : Fin 280) (hi : i ∈ nineCoverIndices 61) :
    nineCodeMem 61 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 61).all (fun i => decide (nineCodeMem 61 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 61, nineCodeMem 61 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_62 (i : Fin 280) (hi : i ∈ nineCoverIndices 62) :
    nineCodeMem 62 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 62).all (fun i => decide (nineCodeMem 62 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 62, nineCodeMem 62 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_63 (i : Fin 280) (hi : i ∈ nineCoverIndices 63) :
    nineCodeMem 63 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 63).all (fun i => decide (nineCodeMem 63 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 63, nineCodeMem 63 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_64 (i : Fin 280) (hi : i ∈ nineCoverIndices 64) :
    nineCodeMem 64 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 64).all (fun i => decide (nineCodeMem 64 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 64, nineCodeMem 64 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_65 (i : Fin 280) (hi : i ∈ nineCoverIndices 65) :
    nineCodeMem 65 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 65).all (fun i => decide (nineCodeMem 65 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 65, nineCodeMem 65 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_66 (i : Fin 280) (hi : i ∈ nineCoverIndices 66) :
    nineCodeMem 66 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 66).all (fun i => decide (nineCodeMem 66 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 66, nineCodeMem 66 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_67 (i : Fin 280) (hi : i ∈ nineCoverIndices 67) :
    nineCodeMem 67 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 67).all (fun i => decide (nineCodeMem 67 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 67, nineCodeMem 67 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_68 (i : Fin 280) (hi : i ∈ nineCoverIndices 68) :
    nineCodeMem 68 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 68).all (fun i => decide (nineCodeMem 68 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 68, nineCodeMem 68 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_69 (i : Fin 280) (hi : i ∈ nineCoverIndices 69) :
    nineCodeMem 69 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 69).all (fun i => decide (nineCodeMem 69 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 69, nineCodeMem 69 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_70 (i : Fin 280) (hi : i ∈ nineCoverIndices 70) :
    nineCodeMem 70 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 70).all (fun i => decide (nineCodeMem 70 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 70, nineCodeMem 70 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_71 (i : Fin 280) (hi : i ∈ nineCoverIndices 71) :
    nineCodeMem 71 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 71).all (fun i => decide (nineCodeMem 71 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 71, nineCodeMem 71 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_72 (i : Fin 280) (hi : i ∈ nineCoverIndices 72) :
    nineCodeMem 72 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 72).all (fun i => decide (nineCodeMem 72 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 72, nineCodeMem 72 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_73 (i : Fin 280) (hi : i ∈ nineCoverIndices 73) :
    nineCodeMem 73 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 73).all (fun i => decide (nineCodeMem 73 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 73, nineCodeMem 73 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_74 (i : Fin 280) (hi : i ∈ nineCoverIndices 74) :
    nineCodeMem 74 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 74).all (fun i => decide (nineCodeMem 74 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 74, nineCodeMem 74 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_75 (i : Fin 280) (hi : i ∈ nineCoverIndices 75) :
    nineCodeMem 75 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 75).all (fun i => decide (nineCodeMem 75 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 75, nineCodeMem 75 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_76 (i : Fin 280) (hi : i ∈ nineCoverIndices 76) :
    nineCodeMem 76 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 76).all (fun i => decide (nineCodeMem 76 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 76, nineCodeMem 76 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_77 (i : Fin 280) (hi : i ∈ nineCoverIndices 77) :
    nineCodeMem 77 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 77).all (fun i => decide (nineCodeMem 77 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 77, nineCodeMem 77 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_78 (i : Fin 280) (hi : i ∈ nineCoverIndices 78) :
    nineCodeMem 78 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 78).all (fun i => decide (nineCodeMem 78 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 78, nineCodeMem 78 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_79 (i : Fin 280) (hi : i ∈ nineCoverIndices 79) :
    nineCodeMem 79 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 79).all (fun i => decide (nineCodeMem 79 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 79, nineCodeMem 79 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_80 (i : Fin 280) (hi : i ∈ nineCoverIndices 80) :
    nineCodeMem 80 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 80).all (fun i => decide (nineCodeMem 80 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 80, nineCodeMem 80 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_81 (i : Fin 280) (hi : i ∈ nineCoverIndices 81) :
    nineCodeMem 81 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 81).all (fun i => decide (nineCodeMem 81 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 81, nineCodeMem 81 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_82 (i : Fin 280) (hi : i ∈ nineCoverIndices 82) :
    nineCodeMem 82 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 82).all (fun i => decide (nineCodeMem 82 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 82, nineCodeMem 82 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound_83 (i : Fin 280) (hi : i ∈ nineCoverIndices 83) :
    nineCodeMem 83 (ninePartitionCode i) := by
  have hc : (nineCoverIndices 83).all (fun i => decide (nineCodeMem 83 (ninePartitionCode i))) = true := by decide +kernel
  have h : ∀ i ∈ nineCoverIndices 83, nineCodeMem 83 (ninePartitionCode i) := by
    simpa only [List.all_eq_true,decide_eq_true_eq] using hc
  exact h i hi

theorem nineCover_sound (e : Fin 84) (i : Fin 280) (hi : i ∈ nineCoverIndices e) :
    nineCodeMem e (ninePartitionCode i) := by
  fin_cases e
  · exact nineCover_sound_0 i hi
  · exact nineCover_sound_1 i hi
  · exact nineCover_sound_2 i hi
  · exact nineCover_sound_3 i hi
  · exact nineCover_sound_4 i hi
  · exact nineCover_sound_5 i hi
  · exact nineCover_sound_6 i hi
  · exact nineCover_sound_7 i hi
  · exact nineCover_sound_8 i hi
  · exact nineCover_sound_9 i hi
  · exact nineCover_sound_10 i hi
  · exact nineCover_sound_11 i hi
  · exact nineCover_sound_12 i hi
  · exact nineCover_sound_13 i hi
  · exact nineCover_sound_14 i hi
  · exact nineCover_sound_15 i hi
  · exact nineCover_sound_16 i hi
  · exact nineCover_sound_17 i hi
  · exact nineCover_sound_18 i hi
  · exact nineCover_sound_19 i hi
  · exact nineCover_sound_20 i hi
  · exact nineCover_sound_21 i hi
  · exact nineCover_sound_22 i hi
  · exact nineCover_sound_23 i hi
  · exact nineCover_sound_24 i hi
  · exact nineCover_sound_25 i hi
  · exact nineCover_sound_26 i hi
  · exact nineCover_sound_27 i hi
  · exact nineCover_sound_28 i hi
  · exact nineCover_sound_29 i hi
  · exact nineCover_sound_30 i hi
  · exact nineCover_sound_31 i hi
  · exact nineCover_sound_32 i hi
  · exact nineCover_sound_33 i hi
  · exact nineCover_sound_34 i hi
  · exact nineCover_sound_35 i hi
  · exact nineCover_sound_36 i hi
  · exact nineCover_sound_37 i hi
  · exact nineCover_sound_38 i hi
  · exact nineCover_sound_39 i hi
  · exact nineCover_sound_40 i hi
  · exact nineCover_sound_41 i hi
  · exact nineCover_sound_42 i hi
  · exact nineCover_sound_43 i hi
  · exact nineCover_sound_44 i hi
  · exact nineCover_sound_45 i hi
  · exact nineCover_sound_46 i hi
  · exact nineCover_sound_47 i hi
  · exact nineCover_sound_48 i hi
  · exact nineCover_sound_49 i hi
  · exact nineCover_sound_50 i hi
  · exact nineCover_sound_51 i hi
  · exact nineCover_sound_52 i hi
  · exact nineCover_sound_53 i hi
  · exact nineCover_sound_54 i hi
  · exact nineCover_sound_55 i hi
  · exact nineCover_sound_56 i hi
  · exact nineCover_sound_57 i hi
  · exact nineCover_sound_58 i hi
  · exact nineCover_sound_59 i hi
  · exact nineCover_sound_60 i hi
  · exact nineCover_sound_61 i hi
  · exact nineCover_sound_62 i hi
  · exact nineCover_sound_63 i hi
  · exact nineCover_sound_64 i hi
  · exact nineCover_sound_65 i hi
  · exact nineCover_sound_66 i hi
  · exact nineCover_sound_67 i hi
  · exact nineCover_sound_68 i hi
  · exact nineCover_sound_69 i hi
  · exact nineCover_sound_70 i hi
  · exact nineCover_sound_71 i hi
  · exact nineCover_sound_72 i hi
  · exact nineCover_sound_73 i hi
  · exact nineCover_sound_74 i hi
  · exact nineCover_sound_75 i hi
  · exact nineCover_sound_76 i hi
  · exact nineCover_sound_77 i hi
  · exact nineCover_sound_78 i hi
  · exact nineCover_sound_79 i hi
  · exact nineCover_sound_80 i hi
  · exact nineCover_sound_81 i hi
  · exact nineCover_sound_82 i hi
  · exact nineCover_sound_83 i hi

end RigidGHZ.Finite
