module

public import RigidGHZ.Finite.ExactCoverSAT

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.U15
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 15) 15 50 10 where
  vertex i := i
  edge i := (#[
  {6,7,9},
  {1,2,8},
  {3,4,5},
  {0,10,12},
  {11,13,14},
  {4,6,13},
  {0,2,5},
  {3,8,10},
  {7,9,11},
  {1,12,14},
  {5,6,7},
  {0,2,8},
  {1,3,4},
  {10,11,12},
  {9,13,14},
  {6,9,10},
  {3,5,7},
  {2,4,8},
  {0,12,13},
  {1,11,14},
  {3,6,9},
  {1,7,11},
  {4,5,8},
  {2,10,13},
  {0,12,14},
  {5,6,10},
  {4,7,11},
  {3,8,9},
  {1,12,13},
  {0,2,14},
  {6,8,14},
  {1,4,7},
  {0,2,3},
  {9,10,13},
  {5,11,12},
  {3,6,11},
  {7,8,9},
  {1,5,13},
  {2,4,12},
  {0,10,14},
  {3,6,13},
  {5,7,8},
  {0,10,11},
  {1,2,9},
  {4,12,14},
  {0,4,8},
  {1,6,14},
  {5,9,11},
  {3,10,13},
  {2,7,12}] : Array (Finset (Fin 15)))[i.val]!
  through i := (#[
  [3,6,11,18,24,29,32,39,42,45],
  [1,9,12,19,21,28,31,37,43,46],
  [1,6,11,17,23,29,32,38,43,49],
  [2,7,12,16,20,27,32,35,40,48],
  [2,5,12,17,22,26,31,38,44,45],
  [2,6,10,16,22,25,34,37,41,47],
  [0,5,10,15,20,25,30,35,40,46],
  [0,8,10,16,21,26,31,36,41,49],
  [1,7,11,17,22,27,30,36,41,45],
  [0,8,14,15,20,27,33,36,43,47],
  [3,7,13,15,23,25,33,39,42,48],
  [4,8,13,19,21,26,34,35,42,47],
  [3,9,13,18,24,28,34,38,44,49],
  [4,5,14,18,23,28,33,37,40,48],
  [4,9,14,19,24,29,30,39,44,46]] : Array (List (Fin 50)))[i.val]!
  row i := (#[
  [0,1,2,3,4],
  [5,6,7,8,9],
  [10,11,12,13,14],
  [15,16,17,18,19],
  [20,21,22,23,24],
  [25,26,27,28,29],
  [30,31,32,33,34],
  [35,36,37,38,39],
  [40,41,42,43,44],
  [45,46,47,48,49]] : Array (List (Fin 50)))[i.val]!

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

end RigidGHZ.Finite.Seeds.U15
