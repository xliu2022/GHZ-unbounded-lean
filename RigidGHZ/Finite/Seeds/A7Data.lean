module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A7
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 7) 21 28 4 where
  vertex i := (#[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6)] : Array (Fin 3 × ZMod 7))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,5)},
  {(0,2),(1,2),(2,3)},
  {(0,3),(1,3),(2,1)},
  {(0,4),(1,4),(2,6)},
  {(0,5),(1,5),(2,4)},
  {(0,6),(1,6),(2,2)},
  {(0,0),(1,1),(2,6)},
  {(0,1),(1,2),(2,4)},
  {(0,2),(1,3),(2,2)},
  {(0,3),(1,4),(2,0)},
  {(0,4),(1,5),(2,5)},
  {(0,5),(1,6),(2,3)},
  {(0,6),(1,0),(2,1)},
  {(0,0),(1,2),(2,5)},
  {(0,1),(1,3),(2,3)},
  {(0,2),(1,4),(2,1)},
  {(0,3),(1,5),(2,6)},
  {(0,4),(1,6),(2,4)},
  {(0,5),(1,0),(2,2)},
  {(0,6),(1,1),(2,0)},
  {(0,0),(1,3),(2,4)},
  {(0,1),(1,4),(2,2)},
  {(0,2),(1,5),(2,0)},
  {(0,3),(1,6),(2,5)},
  {(0,4),(1,0),(2,3)},
  {(0,5),(1,1),(2,1)},
  {(0,6),(1,2),(2,6)}] : Array (Finset (Fin 3 × ZMod 7)))[i.val]!
  through i := (#[
  [0,7,14,21],
  [1,8,15,22],
  [2,9,16,23],
  [3,10,17,24],
  [4,11,18,25],
  [5,12,19,26],
  [6,13,20,27],
  [0,13,19,25],
  [1,7,20,26],
  [2,8,14,27],
  [3,9,15,21],
  [4,10,16,22],
  [5,11,17,23],
  [6,12,18,24],
  [0,10,20,23],
  [3,13,16,26],
  [6,9,19,22],
  [2,12,15,25],
  [5,8,18,21],
  [1,11,14,24],
  [4,7,17,27]] : Array (List (Fin 28)))[i.val]!
  row i := (#[
  [0,1,2,3,4,5,6],
  [7,8,9,10,11,12,13],
  [14,15,16,17,18,19,20],
  [21,22,23,24,25,26,27]] : Array (List (Fin 28)))[i.val]!

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

end RigidGHZ.Finite.Seeds.A7
