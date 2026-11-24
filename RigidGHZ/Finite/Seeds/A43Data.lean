module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed
public import RigidGHZ.Finite.ExactCoverIndex

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A43
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 43) 129 215 5 where
  vertex i := (#[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18),(1,19),(1,20),(1,21),(1,22),(1,23),(1,24),(1,25),(1,26),(1,27),(1,28),(1,29),(1,30),(1,31),(1,32),(1,33),(1,34),(1,35),(1,36),(1,37),(1,38),(1,39),(1,40),(1,41),(1,42),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,32),(2,33),(2,34),(2,35),(2,36),(2,37),(2,38),(2,39),(2,40),(2,41),(2,42)] : Array (Fin 3 × ZMod 43))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,41)},
  {(0,2),(1,2),(2,39)},
  {(0,3),(1,3),(2,37)},
  {(0,4),(1,4),(2,35)},
  {(0,5),(1,5),(2,33)},
  {(0,6),(1,6),(2,31)},
  {(0,7),(1,7),(2,29)},
  {(0,8),(1,8),(2,27)},
  {(0,9),(1,9),(2,25)},
  {(0,10),(1,10),(2,23)},
  {(0,11),(1,11),(2,21)},
  {(0,12),(1,12),(2,19)},
  {(0,13),(1,13),(2,17)},
  {(0,14),(1,14),(2,15)},
  {(0,15),(1,15),(2,13)},
  {(0,16),(1,16),(2,11)},
  {(0,17),(1,17),(2,9)},
  {(0,18),(1,18),(2,7)},
  {(0,19),(1,19),(2,5)},
  {(0,20),(1,20),(2,3)},
  {(0,21),(1,21),(2,1)},
  {(0,22),(1,22),(2,42)},
  {(0,23),(1,23),(2,40)},
  {(0,24),(1,24),(2,38)},
  {(0,25),(1,25),(2,36)},
  {(0,26),(1,26),(2,34)},
  {(0,27),(1,27),(2,32)},
  {(0,28),(1,28),(2,30)},
  {(0,29),(1,29),(2,28)},
  {(0,30),(1,30),(2,26)},
  {(0,31),(1,31),(2,24)},
  {(0,32),(1,32),(2,22)},
  {(0,33),(1,33),(2,20)},
  {(0,34),(1,34),(2,18)},
  {(0,35),(1,35),(2,16)},
  {(0,36),(1,36),(2,14)},
  {(0,37),(1,37),(2,12)},
  {(0,38),(1,38),(2,10)},
  {(0,39),(1,39),(2,8)},
  {(0,40),(1,40),(2,6)},
  {(0,41),(1,41),(2,4)},
  {(0,42),(1,42),(2,2)},
  {(0,0),(1,1),(2,42)},
  {(0,1),(1,2),(2,40)},
  {(0,2),(1,3),(2,38)},
  {(0,3),(1,4),(2,36)},
  {(0,4),(1,5),(2,34)},
  {(0,5),(1,6),(2,32)},
  {(0,6),(1,7),(2,30)},
  {(0,7),(1,8),(2,28)},
  {(0,8),(1,9),(2,26)},
  {(0,9),(1,10),(2,24)},
  {(0,10),(1,11),(2,22)},
  {(0,11),(1,12),(2,20)},
  {(0,12),(1,13),(2,18)},
  {(0,13),(1,14),(2,16)},
  {(0,14),(1,15),(2,14)},
  {(0,15),(1,16),(2,12)},
  {(0,16),(1,17),(2,10)},
  {(0,17),(1,18),(2,8)},
  {(0,18),(1,19),(2,6)},
  {(0,19),(1,20),(2,4)},
  {(0,20),(1,21),(2,2)},
  {(0,21),(1,22),(2,0)},
  {(0,22),(1,23),(2,41)},
  {(0,23),(1,24),(2,39)},
  {(0,24),(1,25),(2,37)},
  {(0,25),(1,26),(2,35)},
  {(0,26),(1,27),(2,33)},
  {(0,27),(1,28),(2,31)},
  {(0,28),(1,29),(2,29)},
  {(0,29),(1,30),(2,27)},
  {(0,30),(1,31),(2,25)},
  {(0,31),(1,32),(2,23)},
  {(0,32),(1,33),(2,21)},
  {(0,33),(1,34),(2,19)},
  {(0,34),(1,35),(2,17)},
  {(0,35),(1,36),(2,15)},
  {(0,36),(1,37),(2,13)},
  {(0,37),(1,38),(2,11)},
  {(0,38),(1,39),(2,9)},
  {(0,39),(1,40),(2,7)},
  {(0,40),(1,41),(2,5)},
  {(0,41),(1,42),(2,3)},
  {(0,42),(1,0),(2,1)},
  {(0,0),(1,2),(2,41)},
  {(0,1),(1,3),(2,39)},
  {(0,2),(1,4),(2,37)},
  {(0,3),(1,5),(2,35)},
  {(0,4),(1,6),(2,33)},
  {(0,5),(1,7),(2,31)},
  {(0,6),(1,8),(2,29)},
  {(0,7),(1,9),(2,27)},
  {(0,8),(1,10),(2,25)},
  {(0,9),(1,11),(2,23)},
  {(0,10),(1,12),(2,21)},
  {(0,11),(1,13),(2,19)},
  {(0,12),(1,14),(2,17)},
  {(0,13),(1,15),(2,15)},
  {(0,14),(1,16),(2,13)},
  {(0,15),(1,17),(2,11)},
  {(0,16),(1,18),(2,9)},
  {(0,17),(1,19),(2,7)},
  {(0,18),(1,20),(2,5)},
  {(0,19),(1,21),(2,3)},
  {(0,20),(1,22),(2,1)},
  {(0,21),(1,23),(2,42)},
  {(0,22),(1,24),(2,40)},
  {(0,23),(1,25),(2,38)},
  {(0,24),(1,26),(2,36)},
  {(0,25),(1,27),(2,34)},
  {(0,26),(1,28),(2,32)},
  {(0,27),(1,29),(2,30)},
  {(0,28),(1,30),(2,28)},
  {(0,29),(1,31),(2,26)},
  {(0,30),(1,32),(2,24)},
  {(0,31),(1,33),(2,22)},
  {(0,32),(1,34),(2,20)},
  {(0,33),(1,35),(2,18)},
  {(0,34),(1,36),(2,16)},
  {(0,35),(1,37),(2,14)},
  {(0,36),(1,38),(2,12)},
  {(0,37),(1,39),(2,10)},
  {(0,38),(1,40),(2,8)},
  {(0,39),(1,41),(2,6)},
  {(0,40),(1,42),(2,4)},
  {(0,41),(1,0),(2,2)},
  {(0,42),(1,1),(2,0)},
  {(0,0),(1,5),(2,38)},
  {(0,1),(1,6),(2,36)},
  {(0,2),(1,7),(2,34)},
  {(0,3),(1,8),(2,32)},
  {(0,4),(1,9),(2,30)},
  {(0,5),(1,10),(2,28)},
  {(0,6),(1,11),(2,26)},
  {(0,7),(1,12),(2,24)},
  {(0,8),(1,13),(2,22)},
  {(0,9),(1,14),(2,20)},
  {(0,10),(1,15),(2,18)},
  {(0,11),(1,16),(2,16)},
  {(0,12),(1,17),(2,14)},
  {(0,13),(1,18),(2,12)},
  {(0,14),(1,19),(2,10)},
  {(0,15),(1,20),(2,8)},
  {(0,16),(1,21),(2,6)},
  {(0,17),(1,22),(2,4)},
  {(0,18),(1,23),(2,2)},
  {(0,19),(1,24),(2,0)},
  {(0,20),(1,25),(2,41)},
  {(0,21),(1,26),(2,39)},
  {(0,22),(1,27),(2,37)},
  {(0,23),(1,28),(2,35)},
  {(0,24),(1,29),(2,33)},
  {(0,25),(1,30),(2,31)},
  {(0,26),(1,31),(2,29)},
  {(0,27),(1,32),(2,27)},
  {(0,28),(1,33),(2,25)},
  {(0,29),(1,34),(2,23)},
  {(0,30),(1,35),(2,21)},
  {(0,31),(1,36),(2,19)},
  {(0,32),(1,37),(2,17)},
  {(0,33),(1,38),(2,15)},
  {(0,34),(1,39),(2,13)},
  {(0,35),(1,40),(2,11)},
  {(0,36),(1,41),(2,9)},
  {(0,37),(1,42),(2,7)},
  {(0,38),(1,0),(2,5)},
  {(0,39),(1,1),(2,3)},
  {(0,40),(1,2),(2,1)},
  {(0,41),(1,3),(2,42)},
  {(0,42),(1,4),(2,40)},
  {(0,0),(1,38),(2,5)},
  {(0,1),(1,39),(2,3)},
  {(0,2),(1,40),(2,1)},
  {(0,3),(1,41),(2,42)},
  {(0,4),(1,42),(2,40)},
  {(0,5),(1,0),(2,38)},
  {(0,6),(1,1),(2,36)},
  {(0,7),(1,2),(2,34)},
  {(0,8),(1,3),(2,32)},
  {(0,9),(1,4),(2,30)},
  {(0,10),(1,5),(2,28)},
  {(0,11),(1,6),(2,26)},
  {(0,12),(1,7),(2,24)},
  {(0,13),(1,8),(2,22)},
  {(0,14),(1,9),(2,20)},
  {(0,15),(1,10),(2,18)},
  {(0,16),(1,11),(2,16)},
  {(0,17),(1,12),(2,14)},
  {(0,18),(1,13),(2,12)},
  {(0,19),(1,14),(2,10)},
  {(0,20),(1,15),(2,8)},
  {(0,21),(1,16),(2,6)},
  {(0,22),(1,17),(2,4)},
  {(0,23),(1,18),(2,2)},
  {(0,24),(1,19),(2,0)},
  {(0,25),(1,20),(2,41)},
  {(0,26),(1,21),(2,39)},
  {(0,27),(1,22),(2,37)},
  {(0,28),(1,23),(2,35)},
  {(0,29),(1,24),(2,33)},
  {(0,30),(1,25),(2,31)},
  {(0,31),(1,26),(2,29)},
  {(0,32),(1,27),(2,27)},
  {(0,33),(1,28),(2,25)},
  {(0,34),(1,29),(2,23)},
  {(0,35),(1,30),(2,21)},
  {(0,36),(1,31),(2,19)},
  {(0,37),(1,32),(2,17)},
  {(0,38),(1,33),(2,15)},
  {(0,39),(1,34),(2,13)},
  {(0,40),(1,35),(2,11)},
  {(0,41),(1,36),(2,9)},
  {(0,42),(1,37),(2,7)}] : Array (Finset (Fin 3 × ZMod 43)))[i.val]!
  through i := (#[
  [0,43,86,129,172],
  [1,44,87,130,173],
  [2,45,88,131,174],
  [3,46,89,132,175],
  [4,47,90,133,176],
  [5,48,91,134,177],
  [6,49,92,135,178],
  [7,50,93,136,179],
  [8,51,94,137,180],
  [9,52,95,138,181],
  [10,53,96,139,182],
  [11,54,97,140,183],
  [12,55,98,141,184],
  [13,56,99,142,185],
  [14,57,100,143,186],
  [15,58,101,144,187],
  [16,59,102,145,188],
  [17,60,103,146,189],
  [18,61,104,147,190],
  [19,62,105,148,191],
  [20,63,106,149,192],
  [21,64,107,150,193],
  [22,65,108,151,194],
  [23,66,109,152,195],
  [24,67,110,153,196],
  [25,68,111,154,197],
  [26,69,112,155,198],
  [27,70,113,156,199],
  [28,71,114,157,200],
  [29,72,115,158,201],
  [30,73,116,159,202],
  [31,74,117,160,203],
  [32,75,118,161,204],
  [33,76,119,162,205],
  [34,77,120,163,206],
  [35,78,121,164,207],
  [36,79,122,165,208],
  [37,80,123,166,209],
  [38,81,124,167,210],
  [39,82,125,168,211],
  [40,83,126,169,212],
  [41,84,127,170,213],
  [42,85,128,171,214],
  [0,85,127,167,177],
  [1,43,128,168,178],
  [2,44,86,169,179],
  [3,45,87,170,180],
  [4,46,88,171,181],
  [5,47,89,129,182],
  [6,48,90,130,183],
  [7,49,91,131,184],
  [8,50,92,132,185],
  [9,51,93,133,186],
  [10,52,94,134,187],
  [11,53,95,135,188],
  [12,54,96,136,189],
  [13,55,97,137,190],
  [14,56,98,138,191],
  [15,57,99,139,192],
  [16,58,100,140,193],
  [17,59,101,141,194],
  [18,60,102,142,195],
  [19,61,103,143,196],
  [20,62,104,144,197],
  [21,63,105,145,198],
  [22,64,106,146,199],
  [23,65,107,147,200],
  [24,66,108,148,201],
  [25,67,109,149,202],
  [26,68,110,150,203],
  [27,69,111,151,204],
  [28,70,112,152,205],
  [29,71,113,153,206],
  [30,72,114,154,207],
  [31,73,115,155,208],
  [32,74,116,156,209],
  [33,75,117,157,210],
  [34,76,118,158,211],
  [35,77,119,159,212],
  [36,78,120,160,213],
  [37,79,121,161,214],
  [38,80,122,162,172],
  [39,81,123,163,173],
  [40,82,124,164,174],
  [41,83,125,165,175],
  [42,84,126,166,176],
  [0,64,128,148,196],
  [21,85,106,169,174],
  [42,63,127,147,195],
  [20,84,105,168,173],
  [41,62,126,146,194],
  [19,83,104,167,172],
  [40,61,125,145,193],
  [18,82,103,166,214],
  [39,60,124,144,192],
  [17,81,102,165,213],
  [38,59,123,143,191],
  [16,80,101,164,212],
  [37,58,122,142,190],
  [15,79,100,163,211],
  [36,57,121,141,189],
  [14,78,99,162,210],
  [35,56,120,140,188],
  [13,77,98,161,209],
  [34,55,119,139,187],
  [12,76,97,160,208],
  [33,54,118,138,186],
  [11,75,96,159,207],
  [32,53,117,137,185],
  [10,74,95,158,206],
  [31,52,116,136,184],
  [9,73,94,157,205],
  [30,51,115,135,183],
  [8,72,93,156,204],
  [29,50,114,134,182],
  [7,71,92,155,203],
  [28,49,113,133,181],
  [6,70,91,154,202],
  [27,48,112,132,180],
  [5,69,90,153,201],
  [26,47,111,131,179],
  [4,68,89,152,200],
  [25,46,110,130,178],
  [3,67,88,151,199],
  [24,45,109,129,177],
  [2,66,87,150,198],
  [23,44,108,171,176],
  [1,65,86,149,197],
  [22,43,107,170,175]] : Array (List (Fin 215)))[i.val]!
  row i := (#[
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42],
  [43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85],
  [86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128],
  [129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171],
  [172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214]] : Array (List (Fin 215)))[i.val]!

def indexShift (r : Fin 5) : ZMod 43 :=
  (#[0,1,2,5,38] : Array (ZMod 43))[r.val]!
def indexRow (i : Fin 215) : Fin 5 := ⟨i.val / 43, by omega⟩
def indexColumn (i : Fin 215) : ZMod 43 := (i.val % 43 : ℕ)

theorem affine_edge_formula : ∀ i, data.edge i = tupleEdge
    (fun j => Supplement.Affine.baseMap (1 : ZMod 43) (indexShift (indexRow i)) j (indexColumn i)) := by
  decide +kernel

theorem index_shift_injective : Function.Injective indexShift := by
  unfold Function.Injective
  decide +kernel

theorem index_parts_injective : Function.Injective (fun i => (indexRow i,indexColumn i)) := by
  intro i j h
  have hd := congrArg (fun x : Fin 5 × ZMod 43 => x.1.val) h
  have hm := congrArg (fun x : Fin 5 × ZMod 43 => x.2.val) h
  change i.val / 43 = j.val / 43 at hd
  have hm' : i.val % 43 = j.val % 43 := by
    simpa [indexColumn,ZMod.val_natCast] using hm
  apply Fin.ext
  omega

theorem table_uniform : ∀ i, (data.edge i).card = 3 := by decide +kernel

theorem table_injective : Function.Injective data.edge := by
  exact affine_table_injective (1 : ZMod 43) indexShift indexRow indexColumn data.edge
    index_shift_injective index_parts_injective affine_edge_formula

theorem table_through_0 : ∀ v : Fin 129,
    0 ≤ v.val → v.val < 8 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_1 : ∀ v : Fin 129,
    8 ≤ v.val → v.val < 16 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_2 : ∀ v : Fin 129,
    16 ≤ v.val → v.val < 24 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_3 : ∀ v : Fin 129,
    24 ≤ v.val → v.val < 32 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_4 : ∀ v : Fin 129,
    32 ≤ v.val → v.val < 40 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_5 : ∀ v : Fin 129,
    40 ≤ v.val → v.val < 48 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_6 : ∀ v : Fin 129,
    48 ≤ v.val → v.val < 56 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_7 : ∀ v : Fin 129,
    56 ≤ v.val → v.val < 64 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_8 : ∀ v : Fin 129,
    64 ≤ v.val → v.val < 72 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_9 : ∀ v : Fin 129,
    72 ≤ v.val → v.val < 80 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_10 : ∀ v : Fin 129,
    80 ≤ v.val → v.val < 88 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_11 : ∀ v : Fin 129,
    88 ≤ v.val → v.val < 96 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_12 : ∀ v : Fin 129,
    96 ≤ v.val → v.val < 104 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_13 : ∀ v : Fin 129,
    104 ≤ v.val → v.val < 112 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_14 : ∀ v : Fin 129,
    112 ≤ v.val → v.val < 120 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_15 : ∀ v : Fin 129,
    120 ≤ v.val → v.val < 128 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_16 : ∀ v : Fin 129,
    128 ≤ v.val → v.val < 136 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  have checks : ∀ b : Fin 17, ∀ v : Fin 129,
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
    · exact table_through_16
  intro v i hi
  exact checks ⟨v.val/8,by omega⟩ v
    (by change (v.val/8)*8 ≤ v.val; omega)
    (by change v.val < (v.val/8+1)*8; omega) i hi

theorem table_counts_0 : ∀ v : Fin 3 × ZMod 43,
    ((data.row 0).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_1 : ∀ v : Fin 3 × ZMod 43,
    ((data.row 1).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_2 : ∀ v : Fin 3 × ZMod 43,
    ((data.row 2).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_3 : ∀ v : Fin 3 × ZMod 43,
    ((data.row 3).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_4 : ∀ v : Fin 3 × ZMod 43,
    ((data.row 4).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod 43,
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

end RigidGHZ.Finite.Seeds.A43
