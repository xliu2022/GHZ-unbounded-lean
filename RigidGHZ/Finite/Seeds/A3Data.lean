module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A3
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 3) 9 9 3 where
  vertex i := (#[(0,0),(0,1),(0,2),(1,0),(1,1),(1,2),(2,0),(2,1),(2,2)] : Array (Fin 3 × ZMod 3))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,1)},
  {(0,2),(1,2),(2,2)},
  {(0,0),(1,1),(2,2)},
  {(0,1),(1,2),(2,0)},
  {(0,2),(1,0),(2,1)},
  {(0,0),(1,2),(2,1)},
  {(0,1),(1,0),(2,2)},
  {(0,2),(1,1),(2,0)}] : Array (Finset (Fin 3 × ZMod 3)))[i.val]!
  through i := (#[
  [0,3,6],
  [1,4,7],
  [2,5,8],
  [0,5,7],
  [1,3,8],
  [2,4,6],
  [0,4,8],
  [1,5,6],
  [2,3,7]] : Array (List (Fin 9)))[i.val]!
  row i := (#[
  [0,1,2],
  [3,4,5],
  [6,7,8]] : Array (List (Fin 9)))[i.val]!

theorem valid : ExactCoverValid data := by
  constructor
  · decide +kernel
  · unfold Function.Injective
    decide +kernel
  · decide +kernel
  · unfold PerfectMatching
    decide +kernel
  · unfold Pairwise
    decide +kernel
  · decide +kernel

theorem uniform : Uniform data.host 3 := valid.host_uniform

end RigidGHZ.Finite.Seeds.A3
