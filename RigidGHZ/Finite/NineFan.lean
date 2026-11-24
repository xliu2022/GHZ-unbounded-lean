module

public import RigidGHZ.Finite.NineFanCheck0
public import RigidGHZ.Finite.NineFanCheck1
public import RigidGHZ.Finite.NineFanCheck2
public import RigidGHZ.Finite.NineFanCheck3
public import RigidGHZ.Finite.NineFanCheck4
public import RigidGHZ.Finite.NineFanCheck5

@[expose] public section
namespace RigidGHZ.Finite

theorem nineFan_valid (i : Fin 756) : (nineFan i).Valid := by
  have h : ∀ j : Fin 36, ∀ r : Fin 21,
      (nineFan ⟨j.val*21+r.val,by omega⟩).Valid := by
    intro j
    fin_cases j
    · exact nineFan_valid_0
    · exact nineFan_valid_1
    · exact nineFan_valid_2
    · exact nineFan_valid_3
    · exact nineFan_valid_4
    · exact nineFan_valid_5
    · exact nineFan_valid_6
    · exact nineFan_valid_7
    · exact nineFan_valid_8
    · exact nineFan_valid_9
    · exact nineFan_valid_10
    · exact nineFan_valid_11
    · exact nineFan_valid_12
    · exact nineFan_valid_13
    · exact nineFan_valid_14
    · exact nineFan_valid_15
    · exact nineFan_valid_16
    · exact nineFan_valid_17
    · exact nineFan_valid_18
    · exact nineFan_valid_19
    · exact nineFan_valid_20
    · exact nineFan_valid_21
    · exact nineFan_valid_22
    · exact nineFan_valid_23
    · exact nineFan_valid_24
    · exact nineFan_valid_25
    · exact nineFan_valid_26
    · exact nineFan_valid_27
    · exact nineFan_valid_28
    · exact nineFan_valid_29
    · exact nineFan_valid_30
    · exact nineFan_valid_31
    · exact nineFan_valid_32
    · exact nineFan_valid_33
    · exact nineFan_valid_34
    · exact nineFan_valid_35
  let j : Fin 36 := ⟨i.val/21,by omega⟩
  let r : Fin 21 := ⟨i.val%21,Nat.mod_lt _ (by decide)⟩
  have hi : (⟨j.val*21+r.val,by omega⟩ : Fin 756) = i := by
    apply Fin.ext
    dsimp [j,r]
    omega
  simpa only [hi] using h j r

end RigidGHZ.Finite
