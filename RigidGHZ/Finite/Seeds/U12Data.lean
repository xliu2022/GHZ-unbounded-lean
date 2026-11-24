module

public import RigidGHZ.Finite.ExactCoverSAT

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.U12
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 12) 12 48 12 where
  vertex i := i
  edge i := (#[
  {2,5,11},
  {1,3,9},
  {4,6,7},
  {0,8,10},
  {0,3,11},
  {7,8,9},
  {2,4,10},
  {1,5,6},
  {0,2,3},
  {1,7,9},
  {5,8,10},
  {4,6,11},
  {5,10,11},
  {1,2,7},
  {3,6,8},
  {0,4,9},
  {1,2,4},
  {3,6,10},
  {0,5,7},
  {8,9,11},
  {0,2,5},
  {3,7,11},
  {6,9,10},
  {1,4,8},
  {2,8,9},
  {1,4,10},
  {0,6,11},
  {3,5,7},
  {4,5,9},
  {7,10,11},
  {0,6,8},
  {1,2,3},
  {3,9,10},
  {2,5,8},
  {1,6,11},
  {0,4,7},
  {3,7,8},
  {4,5,6},
  {1,2,11},
  {0,9,10},
  {1,8,10},
  {2,6,9},
  {0,7,11},
  {3,4,5},
  {0,3,8},
  {2,6,10},
  {1,5,7},
  {4,9,11}] : Array (Finset (Fin 12)))[i.val]!
  through i := (#[
  [3,4,8,15,18,20,26,30,35,39,42,44],
  [1,7,9,13,16,23,25,31,34,38,40,46],
  [0,6,8,13,16,20,24,31,33,38,41,45],
  [1,4,8,14,17,21,27,31,32,36,43,44],
  [2,6,11,15,16,23,25,28,35,37,43,47],
  [0,7,10,12,18,20,27,28,33,37,43,46],
  [2,7,11,14,17,22,26,30,34,37,41,45],
  [2,5,9,13,18,21,27,29,35,36,42,46],
  [3,5,10,14,19,23,24,30,33,36,40,44],
  [1,5,9,15,19,22,24,28,32,39,41,47],
  [3,6,10,12,17,22,25,29,32,39,40,45],
  [0,4,11,12,19,21,26,29,34,38,42,47]] : Array (List (Fin 48)))[i.val]!
  row i := (#[
  [0,1,2,3],
  [4,5,6,7],
  [8,9,10,11],
  [12,13,14,15],
  [16,17,18,19],
  [20,21,22,23],
  [24,25,26,27],
  [28,29,30,31],
  [32,33,34,35],
  [36,37,38,39],
  [40,41,42,43],
  [44,45,46,47]] : Array (List (Fin 48)))[i.val]!

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

end RigidGHZ.Finite.Seeds.U12
