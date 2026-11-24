module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A5
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 5) 15 20 4 where
  vertex i := (#[(0,0),(0,1),(0,2),(0,3),(0,4),(1,0),(1,1),(1,2),(1,3),(1,4),(2,0),(2,1),(2,2),(2,3),(2,4)] : Array (Fin 3 × ZMod 5))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,3)},
  {(0,2),(1,2),(2,1)},
  {(0,3),(1,3),(2,4)},
  {(0,4),(1,4),(2,2)},
  {(0,0),(1,1),(2,4)},
  {(0,1),(1,2),(2,2)},
  {(0,2),(1,3),(2,0)},
  {(0,3),(1,4),(2,3)},
  {(0,4),(1,0),(2,1)},
  {(0,0),(1,2),(2,3)},
  {(0,1),(1,3),(2,1)},
  {(0,2),(1,4),(2,4)},
  {(0,3),(1,0),(2,2)},
  {(0,4),(1,1),(2,0)},
  {(0,0),(1,3),(2,2)},
  {(0,1),(1,4),(2,0)},
  {(0,2),(1,0),(2,3)},
  {(0,3),(1,1),(2,1)},
  {(0,4),(1,2),(2,4)}] : Array (Finset (Fin 3 × ZMod 5)))[i.val]!
  through i := (#[
  [0,5,10,15],
  [1,6,11,16],
  [2,7,12,17],
  [3,8,13,18],
  [4,9,14,19],
  [0,9,13,17],
  [1,5,14,18],
  [2,6,10,19],
  [3,7,11,15],
  [4,8,12,16],
  [0,7,14,16],
  [2,9,11,18],
  [4,6,13,15],
  [1,8,10,17],
  [3,5,12,19]] : Array (List (Fin 20)))[i.val]!
  row i := (#[
  [0,1,2,3,4],
  [5,6,7,8,9],
  [10,11,12,13,14],
  [15,16,17,18,19]] : Array (List (Fin 20)))[i.val]!

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

end RigidGHZ.Finite.Seeds.A5
