module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed
public import RigidGHZ.Finite.ExactCoverIndex

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A41
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 41) 123 205 5 where
  vertex i := (#[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18),(1,19),(1,20),(1,21),(1,22),(1,23),(1,24),(1,25),(1,26),(1,27),(1,28),(1,29),(1,30),(1,31),(1,32),(1,33),(1,34),(1,35),(1,36),(1,37),(1,38),(1,39),(1,40),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,32),(2,33),(2,34),(2,35),(2,36),(2,37),(2,38),(2,39),(2,40)] : Array (Fin 3 × ZMod 41))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,39)},
  {(0,2),(1,2),(2,37)},
  {(0,3),(1,3),(2,35)},
  {(0,4),(1,4),(2,33)},
  {(0,5),(1,5),(2,31)},
  {(0,6),(1,6),(2,29)},
  {(0,7),(1,7),(2,27)},
  {(0,8),(1,8),(2,25)},
  {(0,9),(1,9),(2,23)},
  {(0,10),(1,10),(2,21)},
  {(0,11),(1,11),(2,19)},
  {(0,12),(1,12),(2,17)},
  {(0,13),(1,13),(2,15)},
  {(0,14),(1,14),(2,13)},
  {(0,15),(1,15),(2,11)},
  {(0,16),(1,16),(2,9)},
  {(0,17),(1,17),(2,7)},
  {(0,18),(1,18),(2,5)},
  {(0,19),(1,19),(2,3)},
  {(0,20),(1,20),(2,1)},
  {(0,21),(1,21),(2,40)},
  {(0,22),(1,22),(2,38)},
  {(0,23),(1,23),(2,36)},
  {(0,24),(1,24),(2,34)},
  {(0,25),(1,25),(2,32)},
  {(0,26),(1,26),(2,30)},
  {(0,27),(1,27),(2,28)},
  {(0,28),(1,28),(2,26)},
  {(0,29),(1,29),(2,24)},
  {(0,30),(1,30),(2,22)},
  {(0,31),(1,31),(2,20)},
  {(0,32),(1,32),(2,18)},
  {(0,33),(1,33),(2,16)},
  {(0,34),(1,34),(2,14)},
  {(0,35),(1,35),(2,12)},
  {(0,36),(1,36),(2,10)},
  {(0,37),(1,37),(2,8)},
  {(0,38),(1,38),(2,6)},
  {(0,39),(1,39),(2,4)},
  {(0,40),(1,40),(2,2)},
  {(0,0),(1,1),(2,40)},
  {(0,1),(1,2),(2,38)},
  {(0,2),(1,3),(2,36)},
  {(0,3),(1,4),(2,34)},
  {(0,4),(1,5),(2,32)},
  {(0,5),(1,6),(2,30)},
  {(0,6),(1,7),(2,28)},
  {(0,7),(1,8),(2,26)},
  {(0,8),(1,9),(2,24)},
  {(0,9),(1,10),(2,22)},
  {(0,10),(1,11),(2,20)},
  {(0,11),(1,12),(2,18)},
  {(0,12),(1,13),(2,16)},
  {(0,13),(1,14),(2,14)},
  {(0,14),(1,15),(2,12)},
  {(0,15),(1,16),(2,10)},
  {(0,16),(1,17),(2,8)},
  {(0,17),(1,18),(2,6)},
  {(0,18),(1,19),(2,4)},
  {(0,19),(1,20),(2,2)},
  {(0,20),(1,21),(2,0)},
  {(0,21),(1,22),(2,39)},
  {(0,22),(1,23),(2,37)},
  {(0,23),(1,24),(2,35)},
  {(0,24),(1,25),(2,33)},
  {(0,25),(1,26),(2,31)},
  {(0,26),(1,27),(2,29)},
  {(0,27),(1,28),(2,27)},
  {(0,28),(1,29),(2,25)},
  {(0,29),(1,30),(2,23)},
  {(0,30),(1,31),(2,21)},
  {(0,31),(1,32),(2,19)},
  {(0,32),(1,33),(2,17)},
  {(0,33),(1,34),(2,15)},
  {(0,34),(1,35),(2,13)},
  {(0,35),(1,36),(2,11)},
  {(0,36),(1,37),(2,9)},
  {(0,37),(1,38),(2,7)},
  {(0,38),(1,39),(2,5)},
  {(0,39),(1,40),(2,3)},
  {(0,40),(1,0),(2,1)},
  {(0,0),(1,2),(2,39)},
  {(0,1),(1,3),(2,37)},
  {(0,2),(1,4),(2,35)},
  {(0,3),(1,5),(2,33)},
  {(0,4),(1,6),(2,31)},
  {(0,5),(1,7),(2,29)},
  {(0,6),(1,8),(2,27)},
  {(0,7),(1,9),(2,25)},
  {(0,8),(1,10),(2,23)},
  {(0,9),(1,11),(2,21)},
  {(0,10),(1,12),(2,19)},
  {(0,11),(1,13),(2,17)},
  {(0,12),(1,14),(2,15)},
  {(0,13),(1,15),(2,13)},
  {(0,14),(1,16),(2,11)},
  {(0,15),(1,17),(2,9)},
  {(0,16),(1,18),(2,7)},
  {(0,17),(1,19),(2,5)},
  {(0,18),(1,20),(2,3)},
  {(0,19),(1,21),(2,1)},
  {(0,20),(1,22),(2,40)},
  {(0,21),(1,23),(2,38)},
  {(0,22),(1,24),(2,36)},
  {(0,23),(1,25),(2,34)},
  {(0,24),(1,26),(2,32)},
  {(0,25),(1,27),(2,30)},
  {(0,26),(1,28),(2,28)},
  {(0,27),(1,29),(2,26)},
  {(0,28),(1,30),(2,24)},
  {(0,29),(1,31),(2,22)},
  {(0,30),(1,32),(2,20)},
  {(0,31),(1,33),(2,18)},
  {(0,32),(1,34),(2,16)},
  {(0,33),(1,35),(2,14)},
  {(0,34),(1,36),(2,12)},
  {(0,35),(1,37),(2,10)},
  {(0,36),(1,38),(2,8)},
  {(0,37),(1,39),(2,6)},
  {(0,38),(1,40),(2,4)},
  {(0,39),(1,0),(2,2)},
  {(0,40),(1,1),(2,0)},
  {(0,0),(1,5),(2,36)},
  {(0,1),(1,6),(2,34)},
  {(0,2),(1,7),(2,32)},
  {(0,3),(1,8),(2,30)},
  {(0,4),(1,9),(2,28)},
  {(0,5),(1,10),(2,26)},
  {(0,6),(1,11),(2,24)},
  {(0,7),(1,12),(2,22)},
  {(0,8),(1,13),(2,20)},
  {(0,9),(1,14),(2,18)},
  {(0,10),(1,15),(2,16)},
  {(0,11),(1,16),(2,14)},
  {(0,12),(1,17),(2,12)},
  {(0,13),(1,18),(2,10)},
  {(0,14),(1,19),(2,8)},
  {(0,15),(1,20),(2,6)},
  {(0,16),(1,21),(2,4)},
  {(0,17),(1,22),(2,2)},
  {(0,18),(1,23),(2,0)},
  {(0,19),(1,24),(2,39)},
  {(0,20),(1,25),(2,37)},
  {(0,21),(1,26),(2,35)},
  {(0,22),(1,27),(2,33)},
  {(0,23),(1,28),(2,31)},
  {(0,24),(1,29),(2,29)},
  {(0,25),(1,30),(2,27)},
  {(0,26),(1,31),(2,25)},
  {(0,27),(1,32),(2,23)},
  {(0,28),(1,33),(2,21)},
  {(0,29),(1,34),(2,19)},
  {(0,30),(1,35),(2,17)},
  {(0,31),(1,36),(2,15)},
  {(0,32),(1,37),(2,13)},
  {(0,33),(1,38),(2,11)},
  {(0,34),(1,39),(2,9)},
  {(0,35),(1,40),(2,7)},
  {(0,36),(1,0),(2,5)},
  {(0,37),(1,1),(2,3)},
  {(0,38),(1,2),(2,1)},
  {(0,39),(1,3),(2,40)},
  {(0,40),(1,4),(2,38)},
  {(0,0),(1,16),(2,25)},
  {(0,1),(1,17),(2,23)},
  {(0,2),(1,18),(2,21)},
  {(0,3),(1,19),(2,19)},
  {(0,4),(1,20),(2,17)},
  {(0,5),(1,21),(2,15)},
  {(0,6),(1,22),(2,13)},
  {(0,7),(1,23),(2,11)},
  {(0,8),(1,24),(2,9)},
  {(0,9),(1,25),(2,7)},
  {(0,10),(1,26),(2,5)},
  {(0,11),(1,27),(2,3)},
  {(0,12),(1,28),(2,1)},
  {(0,13),(1,29),(2,40)},
  {(0,14),(1,30),(2,38)},
  {(0,15),(1,31),(2,36)},
  {(0,16),(1,32),(2,34)},
  {(0,17),(1,33),(2,32)},
  {(0,18),(1,34),(2,30)},
  {(0,19),(1,35),(2,28)},
  {(0,20),(1,36),(2,26)},
  {(0,21),(1,37),(2,24)},
  {(0,22),(1,38),(2,22)},
  {(0,23),(1,39),(2,20)},
  {(0,24),(1,40),(2,18)},
  {(0,25),(1,0),(2,16)},
  {(0,26),(1,1),(2,14)},
  {(0,27),(1,2),(2,12)},
  {(0,28),(1,3),(2,10)},
  {(0,29),(1,4),(2,8)},
  {(0,30),(1,5),(2,6)},
  {(0,31),(1,6),(2,4)},
  {(0,32),(1,7),(2,2)},
  {(0,33),(1,8),(2,0)},
  {(0,34),(1,9),(2,39)},
  {(0,35),(1,10),(2,37)},
  {(0,36),(1,11),(2,35)},
  {(0,37),(1,12),(2,33)},
  {(0,38),(1,13),(2,31)},
  {(0,39),(1,14),(2,29)},
  {(0,40),(1,15),(2,27)}] : Array (Finset (Fin 3 × ZMod 41)))[i.val]!
  through i := (#[
  [0,41,82,123,164],
  [1,42,83,124,165],
  [2,43,84,125,166],
  [3,44,85,126,167],
  [4,45,86,127,168],
  [5,46,87,128,169],
  [6,47,88,129,170],
  [7,48,89,130,171],
  [8,49,90,131,172],
  [9,50,91,132,173],
  [10,51,92,133,174],
  [11,52,93,134,175],
  [12,53,94,135,176],
  [13,54,95,136,177],
  [14,55,96,137,178],
  [15,56,97,138,179],
  [16,57,98,139,180],
  [17,58,99,140,181],
  [18,59,100,141,182],
  [19,60,101,142,183],
  [20,61,102,143,184],
  [21,62,103,144,185],
  [22,63,104,145,186],
  [23,64,105,146,187],
  [24,65,106,147,188],
  [25,66,107,148,189],
  [26,67,108,149,190],
  [27,68,109,150,191],
  [28,69,110,151,192],
  [29,70,111,152,193],
  [30,71,112,153,194],
  [31,72,113,154,195],
  [32,73,114,155,196],
  [33,74,115,156,197],
  [34,75,116,157,198],
  [35,76,117,158,199],
  [36,77,118,159,200],
  [37,78,119,160,201],
  [38,79,120,161,202],
  [39,80,121,162,203],
  [40,81,122,163,204],
  [0,81,121,159,189],
  [1,41,122,160,190],
  [2,42,82,161,191],
  [3,43,83,162,192],
  [4,44,84,163,193],
  [5,45,85,123,194],
  [6,46,86,124,195],
  [7,47,87,125,196],
  [8,48,88,126,197],
  [9,49,89,127,198],
  [10,50,90,128,199],
  [11,51,91,129,200],
  [12,52,92,130,201],
  [13,53,93,131,202],
  [14,54,94,132,203],
  [15,55,95,133,204],
  [16,56,96,134,164],
  [17,57,97,135,165],
  [18,58,98,136,166],
  [19,59,99,137,167],
  [20,60,100,138,168],
  [21,61,101,139,169],
  [22,62,102,140,170],
  [23,63,103,141,171],
  [24,64,104,142,172],
  [25,65,105,143,173],
  [26,66,106,144,174],
  [27,67,107,145,175],
  [28,68,108,146,176],
  [29,69,109,147,177],
  [30,70,110,148,178],
  [31,71,111,149,179],
  [32,72,112,150,180],
  [33,73,113,151,181],
  [34,74,114,152,182],
  [35,75,115,153,183],
  [36,76,116,154,184],
  [37,77,117,155,185],
  [38,78,118,156,186],
  [39,79,119,157,187],
  [40,80,120,158,188],
  [0,61,122,141,197],
  [20,81,101,161,176],
  [40,60,121,140,196],
  [19,80,100,160,175],
  [39,59,120,139,195],
  [18,79,99,159,174],
  [38,58,119,138,194],
  [17,78,98,158,173],
  [37,57,118,137,193],
  [16,77,97,157,172],
  [36,56,117,136,192],
  [15,76,96,156,171],
  [35,55,116,135,191],
  [14,75,95,155,170],
  [34,54,115,134,190],
  [13,74,94,154,169],
  [33,53,114,133,189],
  [12,73,93,153,168],
  [32,52,113,132,188],
  [11,72,92,152,167],
  [31,51,112,131,187],
  [10,71,91,151,166],
  [30,50,111,130,186],
  [9,70,90,150,165],
  [29,49,110,129,185],
  [8,69,89,149,164],
  [28,48,109,128,184],
  [7,68,88,148,204],
  [27,47,108,127,183],
  [6,67,87,147,203],
  [26,46,107,126,182],
  [5,66,86,146,202],
  [25,45,106,125,181],
  [4,65,85,145,201],
  [24,44,105,124,180],
  [3,64,84,144,200],
  [23,43,104,123,179],
  [2,63,83,143,199],
  [22,42,103,163,178],
  [1,62,82,142,198],
  [21,41,102,162,177]] : Array (List (Fin 205)))[i.val]!
  row i := (#[
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40],
  [41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81],
  [82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122],
  [123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163],
  [164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204]] : Array (List (Fin 205)))[i.val]!

def indexShift (r : Fin 5) : ZMod 41 :=
  (#[0,1,2,5,16] : Array (ZMod 41))[r.val]!
def indexRow (i : Fin 205) : Fin 5 := ⟨i.val / 41, by omega⟩
def indexColumn (i : Fin 205) : ZMod 41 := (i.val % 41 : ℕ)

theorem affine_edge_formula : ∀ i, data.edge i = tupleEdge
    (fun j => Supplement.Affine.baseMap (1 : ZMod 41) (indexShift (indexRow i)) j (indexColumn i)) := by
  decide +kernel

theorem index_shift_injective : Function.Injective indexShift := by
  unfold Function.Injective
  decide +kernel

theorem index_parts_injective : Function.Injective (fun i => (indexRow i,indexColumn i)) := by
  intro i j h
  have hd := congrArg (fun x : Fin 5 × ZMod 41 => x.1.val) h
  have hm := congrArg (fun x : Fin 5 × ZMod 41 => x.2.val) h
  change i.val / 41 = j.val / 41 at hd
  have hm' : i.val % 41 = j.val % 41 := by
    simpa [indexColumn,ZMod.val_natCast] using hm
  apply Fin.ext
  omega

theorem table_uniform : ∀ i, (data.edge i).card = 3 := by decide +kernel

theorem table_injective : Function.Injective data.edge := by
  exact affine_table_injective (1 : ZMod 41) indexShift indexRow indexColumn data.edge
    index_shift_injective index_parts_injective affine_edge_formula

theorem table_through_0 : ∀ v : Fin 123,
    0 ≤ v.val → v.val < 8 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_1 : ∀ v : Fin 123,
    8 ≤ v.val → v.val < 16 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_2 : ∀ v : Fin 123,
    16 ≤ v.val → v.val < 24 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_3 : ∀ v : Fin 123,
    24 ≤ v.val → v.val < 32 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_4 : ∀ v : Fin 123,
    32 ≤ v.val → v.val < 40 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_5 : ∀ v : Fin 123,
    40 ≤ v.val → v.val < 48 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_6 : ∀ v : Fin 123,
    48 ≤ v.val → v.val < 56 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_7 : ∀ v : Fin 123,
    56 ≤ v.val → v.val < 64 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_8 : ∀ v : Fin 123,
    64 ≤ v.val → v.val < 72 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_9 : ∀ v : Fin 123,
    72 ≤ v.val → v.val < 80 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_10 : ∀ v : Fin 123,
    80 ≤ v.val → v.val < 88 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_11 : ∀ v : Fin 123,
    88 ≤ v.val → v.val < 96 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_12 : ∀ v : Fin 123,
    96 ≤ v.val → v.val < 104 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_13 : ∀ v : Fin 123,
    104 ≤ v.val → v.val < 112 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_14 : ∀ v : Fin 123,
    112 ≤ v.val → v.val < 120 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_15 : ∀ v : Fin 123,
    120 ≤ v.val → v.val < 128 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  have checks : ∀ b : Fin 16, ∀ v : Fin 123,
      b.val*8 ≤ v.val → v.val < (b.val+1)*8 →
      ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
    intro b
    fin_cases b
    · exact table_through_0
    · exact table_through_1
    · exact table_through_2
    · exact table_through_3
    · exact table_through_4
    · exact table_through_5
    · exact table_through_6
    · exact table_through_7
    · exact table_through_8
    · exact table_through_9
    · exact table_through_10
    · exact table_through_11
    · exact table_through_12
    · exact table_through_13
    · exact table_through_14
    · exact table_through_15
  intro v i hi
  exact checks ⟨v.val/8,by omega⟩ v
    (by change (v.val/8)*8 ≤ v.val; omega)
    (by change v.val < (v.val/8+1)*8; omega) i hi

theorem table_counts_0 : ∀ v : Fin 3 × ZMod 41,
    ((data.row 0).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_1 : ∀ v : Fin 3 × ZMod 41,
    ((data.row 1).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_2 : ∀ v : Fin 3 × ZMod 41,
    ((data.row 2).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_3 : ∀ v : Fin 3 × ZMod 41,
    ((data.row 3).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_4 : ∀ v : Fin 3 × ZMod 41,
    ((data.row 4).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod 41,
    ((data.row r).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by
  intro r
  fin_cases r
  · exact table_counts_0
  · exact table_counts_1
  · exact table_counts_2
  · exact table_counts_3
  · exact table_counts_4

theorem table_perfect : ∀ r, PerfectMatching data.host (data.matching r) := by
  intro r
  exact exactCover_perfect_of_indices data table_injective r (table_counts r)

theorem table_index_disjoint_0 : ∀ s : Fin 5, 0 ≠ s →
    Disjoint (data.row 0).toFinset (data.row s).toFinset := by decide +kernel

theorem table_index_disjoint_1 : ∀ s : Fin 5, 1 ≠ s →
    Disjoint (data.row 1).toFinset (data.row s).toFinset := by decide +kernel

theorem table_index_disjoint_2 : ∀ s : Fin 5, 2 ≠ s →
    Disjoint (data.row 2).toFinset (data.row s).toFinset := by decide +kernel

theorem table_index_disjoint_3 : ∀ s : Fin 5, 3 ≠ s →
    Disjoint (data.row 3).toFinset (data.row s).toFinset := by decide +kernel

theorem table_index_disjoint_4 : ∀ s : Fin 5, 4 ≠ s →
    Disjoint (data.row 4).toFinset (data.row s).toFinset := by decide +kernel

theorem table_index_disjoint : Pairwise (fun r s => Disjoint (data.row r).toFinset (data.row s).toFinset) := by
  intro r s hrs
  fin_cases r
  · exact table_index_disjoint_0 s hrs
  · exact table_index_disjoint_1 s hrs
  · exact table_index_disjoint_2 s hrs
  · exact table_index_disjoint_3 s hrs
  · exact table_index_disjoint_4 s hrs

theorem table_disjoint : Pairwise (fun r s => Disjoint (data.matching r) (data.matching s)) := by
  exact exactCover_disjoint_of_indices data table_injective table_index_disjoint

theorem table_index_cover : ∀ i, ∃ r, i ∈ data.row r := by decide +kernel

theorem table_covers : data.host = Finset.univ.biUnion data.matching :=
  exactCover_covers_of_indices data table_index_cover

theorem valid : ExactCoverValid data :=
  ⟨table_uniform,table_injective,table_through,table_perfect,table_disjoint,table_covers⟩

theorem uniform : Uniform data.host 3 := valid.host_uniform

end RigidGHZ.Finite.Seeds.A41
