module

public import RigidGHZ.Finite.ExactCoverSAT
public import RigidGHZ.Supplement.AffineSeed
public import RigidGHZ.Finite.ExactCoverIndex

/-! Exact printed seed data from Supplement S4/S6. -/
@[expose] public section
namespace RigidGHZ.Finite.Seeds.A47
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

def data : ExactCoverData (Fin 3 × ZMod 47) 141 235 5 where
  vertex i := (#[(0,0),(0,1),(0,2),(0,3),(0,4),(0,5),(0,6),(0,7),(0,8),(0,9),(0,10),(0,11),(0,12),(0,13),(0,14),(0,15),(0,16),(0,17),(0,18),(0,19),(0,20),(0,21),(0,22),(0,23),(0,24),(0,25),(0,26),(0,27),(0,28),(0,29),(0,30),(0,31),(0,32),(0,33),(0,34),(0,35),(0,36),(0,37),(0,38),(0,39),(0,40),(0,41),(0,42),(0,43),(0,44),(0,45),(0,46),(1,0),(1,1),(1,2),(1,3),(1,4),(1,5),(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(1,12),(1,13),(1,14),(1,15),(1,16),(1,17),(1,18),(1,19),(1,20),(1,21),(1,22),(1,23),(1,24),(1,25),(1,26),(1,27),(1,28),(1,29),(1,30),(1,31),(1,32),(1,33),(1,34),(1,35),(1,36),(1,37),(1,38),(1,39),(1,40),(1,41),(1,42),(1,43),(1,44),(1,45),(1,46),(2,0),(2,1),(2,2),(2,3),(2,4),(2,5),(2,6),(2,7),(2,8),(2,9),(2,10),(2,11),(2,12),(2,13),(2,14),(2,15),(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22),(2,23),(2,24),(2,25),(2,26),(2,27),(2,28),(2,29),(2,30),(2,31),(2,32),(2,33),(2,34),(2,35),(2,36),(2,37),(2,38),(2,39),(2,40),(2,41),(2,42),(2,43),(2,44),(2,45),(2,46)] : Array (Fin 3 × ZMod 47))[i.val]!
  edge i := (#[
  {(0,0),(1,0),(2,0)},
  {(0,1),(1,1),(2,45)},
  {(0,2),(1,2),(2,43)},
  {(0,3),(1,3),(2,41)},
  {(0,4),(1,4),(2,39)},
  {(0,5),(1,5),(2,37)},
  {(0,6),(1,6),(2,35)},
  {(0,7),(1,7),(2,33)},
  {(0,8),(1,8),(2,31)},
  {(0,9),(1,9),(2,29)},
  {(0,10),(1,10),(2,27)},
  {(0,11),(1,11),(2,25)},
  {(0,12),(1,12),(2,23)},
  {(0,13),(1,13),(2,21)},
  {(0,14),(1,14),(2,19)},
  {(0,15),(1,15),(2,17)},
  {(0,16),(1,16),(2,15)},
  {(0,17),(1,17),(2,13)},
  {(0,18),(1,18),(2,11)},
  {(0,19),(1,19),(2,9)},
  {(0,20),(1,20),(2,7)},
  {(0,21),(1,21),(2,5)},
  {(0,22),(1,22),(2,3)},
  {(0,23),(1,23),(2,1)},
  {(0,24),(1,24),(2,46)},
  {(0,25),(1,25),(2,44)},
  {(0,26),(1,26),(2,42)},
  {(0,27),(1,27),(2,40)},
  {(0,28),(1,28),(2,38)},
  {(0,29),(1,29),(2,36)},
  {(0,30),(1,30),(2,34)},
  {(0,31),(1,31),(2,32)},
  {(0,32),(1,32),(2,30)},
  {(0,33),(1,33),(2,28)},
  {(0,34),(1,34),(2,26)},
  {(0,35),(1,35),(2,24)},
  {(0,36),(1,36),(2,22)},
  {(0,37),(1,37),(2,20)},
  {(0,38),(1,38),(2,18)},
  {(0,39),(1,39),(2,16)},
  {(0,40),(1,40),(2,14)},
  {(0,41),(1,41),(2,12)},
  {(0,42),(1,42),(2,10)},
  {(0,43),(1,43),(2,8)},
  {(0,44),(1,44),(2,6)},
  {(0,45),(1,45),(2,4)},
  {(0,46),(1,46),(2,2)},
  {(0,0),(1,1),(2,46)},
  {(0,1),(1,2),(2,44)},
  {(0,2),(1,3),(2,42)},
  {(0,3),(1,4),(2,40)},
  {(0,4),(1,5),(2,38)},
  {(0,5),(1,6),(2,36)},
  {(0,6),(1,7),(2,34)},
  {(0,7),(1,8),(2,32)},
  {(0,8),(1,9),(2,30)},
  {(0,9),(1,10),(2,28)},
  {(0,10),(1,11),(2,26)},
  {(0,11),(1,12),(2,24)},
  {(0,12),(1,13),(2,22)},
  {(0,13),(1,14),(2,20)},
  {(0,14),(1,15),(2,18)},
  {(0,15),(1,16),(2,16)},
  {(0,16),(1,17),(2,14)},
  {(0,17),(1,18),(2,12)},
  {(0,18),(1,19),(2,10)},
  {(0,19),(1,20),(2,8)},
  {(0,20),(1,21),(2,6)},
  {(0,21),(1,22),(2,4)},
  {(0,22),(1,23),(2,2)},
  {(0,23),(1,24),(2,0)},
  {(0,24),(1,25),(2,45)},
  {(0,25),(1,26),(2,43)},
  {(0,26),(1,27),(2,41)},
  {(0,27),(1,28),(2,39)},
  {(0,28),(1,29),(2,37)},
  {(0,29),(1,30),(2,35)},
  {(0,30),(1,31),(2,33)},
  {(0,31),(1,32),(2,31)},
  {(0,32),(1,33),(2,29)},
  {(0,33),(1,34),(2,27)},
  {(0,34),(1,35),(2,25)},
  {(0,35),(1,36),(2,23)},
  {(0,36),(1,37),(2,21)},
  {(0,37),(1,38),(2,19)},
  {(0,38),(1,39),(2,17)},
  {(0,39),(1,40),(2,15)},
  {(0,40),(1,41),(2,13)},
  {(0,41),(1,42),(2,11)},
  {(0,42),(1,43),(2,9)},
  {(0,43),(1,44),(2,7)},
  {(0,44),(1,45),(2,5)},
  {(0,45),(1,46),(2,3)},
  {(0,46),(1,0),(2,1)},
  {(0,0),(1,2),(2,45)},
  {(0,1),(1,3),(2,43)},
  {(0,2),(1,4),(2,41)},
  {(0,3),(1,5),(2,39)},
  {(0,4),(1,6),(2,37)},
  {(0,5),(1,7),(2,35)},
  {(0,6),(1,8),(2,33)},
  {(0,7),(1,9),(2,31)},
  {(0,8),(1,10),(2,29)},
  {(0,9),(1,11),(2,27)},
  {(0,10),(1,12),(2,25)},
  {(0,11),(1,13),(2,23)},
  {(0,12),(1,14),(2,21)},
  {(0,13),(1,15),(2,19)},
  {(0,14),(1,16),(2,17)},
  {(0,15),(1,17),(2,15)},
  {(0,16),(1,18),(2,13)},
  {(0,17),(1,19),(2,11)},
  {(0,18),(1,20),(2,9)},
  {(0,19),(1,21),(2,7)},
  {(0,20),(1,22),(2,5)},
  {(0,21),(1,23),(2,3)},
  {(0,22),(1,24),(2,1)},
  {(0,23),(1,25),(2,46)},
  {(0,24),(1,26),(2,44)},
  {(0,25),(1,27),(2,42)},
  {(0,26),(1,28),(2,40)},
  {(0,27),(1,29),(2,38)},
  {(0,28),(1,30),(2,36)},
  {(0,29),(1,31),(2,34)},
  {(0,30),(1,32),(2,32)},
  {(0,31),(1,33),(2,30)},
  {(0,32),(1,34),(2,28)},
  {(0,33),(1,35),(2,26)},
  {(0,34),(1,36),(2,24)},
  {(0,35),(1,37),(2,22)},
  {(0,36),(1,38),(2,20)},
  {(0,37),(1,39),(2,18)},
  {(0,38),(1,40),(2,16)},
  {(0,39),(1,41),(2,14)},
  {(0,40),(1,42),(2,12)},
  {(0,41),(1,43),(2,10)},
  {(0,42),(1,44),(2,8)},
  {(0,43),(1,45),(2,6)},
  {(0,44),(1,46),(2,4)},
  {(0,45),(1,0),(2,2)},
  {(0,46),(1,1),(2,0)},
  {(0,0),(1,11),(2,36)},
  {(0,1),(1,12),(2,34)},
  {(0,2),(1,13),(2,32)},
  {(0,3),(1,14),(2,30)},
  {(0,4),(1,15),(2,28)},
  {(0,5),(1,16),(2,26)},
  {(0,6),(1,17),(2,24)},
  {(0,7),(1,18),(2,22)},
  {(0,8),(1,19),(2,20)},
  {(0,9),(1,20),(2,18)},
  {(0,10),(1,21),(2,16)},
  {(0,11),(1,22),(2,14)},
  {(0,12),(1,23),(2,12)},
  {(0,13),(1,24),(2,10)},
  {(0,14),(1,25),(2,8)},
  {(0,15),(1,26),(2,6)},
  {(0,16),(1,27),(2,4)},
  {(0,17),(1,28),(2,2)},
  {(0,18),(1,29),(2,0)},
  {(0,19),(1,30),(2,45)},
  {(0,20),(1,31),(2,43)},
  {(0,21),(1,32),(2,41)},
  {(0,22),(1,33),(2,39)},
  {(0,23),(1,34),(2,37)},
  {(0,24),(1,35),(2,35)},
  {(0,25),(1,36),(2,33)},
  {(0,26),(1,37),(2,31)},
  {(0,27),(1,38),(2,29)},
  {(0,28),(1,39),(2,27)},
  {(0,29),(1,40),(2,25)},
  {(0,30),(1,41),(2,23)},
  {(0,31),(1,42),(2,21)},
  {(0,32),(1,43),(2,19)},
  {(0,33),(1,44),(2,17)},
  {(0,34),(1,45),(2,15)},
  {(0,35),(1,46),(2,13)},
  {(0,36),(1,0),(2,11)},
  {(0,37),(1,1),(2,9)},
  {(0,38),(1,2),(2,7)},
  {(0,39),(1,3),(2,5)},
  {(0,40),(1,4),(2,3)},
  {(0,41),(1,5),(2,1)},
  {(0,42),(1,6),(2,46)},
  {(0,43),(1,7),(2,44)},
  {(0,44),(1,8),(2,42)},
  {(0,45),(1,9),(2,40)},
  {(0,46),(1,10),(2,38)},
  {(0,0),(1,23),(2,24)},
  {(0,1),(1,24),(2,22)},
  {(0,2),(1,25),(2,20)},
  {(0,3),(1,26),(2,18)},
  {(0,4),(1,27),(2,16)},
  {(0,5),(1,28),(2,14)},
  {(0,6),(1,29),(2,12)},
  {(0,7),(1,30),(2,10)},
  {(0,8),(1,31),(2,8)},
  {(0,9),(1,32),(2,6)},
  {(0,10),(1,33),(2,4)},
  {(0,11),(1,34),(2,2)},
  {(0,12),(1,35),(2,0)},
  {(0,13),(1,36),(2,45)},
  {(0,14),(1,37),(2,43)},
  {(0,15),(1,38),(2,41)},
  {(0,16),(1,39),(2,39)},
  {(0,17),(1,40),(2,37)},
  {(0,18),(1,41),(2,35)},
  {(0,19),(1,42),(2,33)},
  {(0,20),(1,43),(2,31)},
  {(0,21),(1,44),(2,29)},
  {(0,22),(1,45),(2,27)},
  {(0,23),(1,46),(2,25)},
  {(0,24),(1,0),(2,23)},
  {(0,25),(1,1),(2,21)},
  {(0,26),(1,2),(2,19)},
  {(0,27),(1,3),(2,17)},
  {(0,28),(1,4),(2,15)},
  {(0,29),(1,5),(2,13)},
  {(0,30),(1,6),(2,11)},
  {(0,31),(1,7),(2,9)},
  {(0,32),(1,8),(2,7)},
  {(0,33),(1,9),(2,5)},
  {(0,34),(1,10),(2,3)},
  {(0,35),(1,11),(2,1)},
  {(0,36),(1,12),(2,46)},
  {(0,37),(1,13),(2,44)},
  {(0,38),(1,14),(2,42)},
  {(0,39),(1,15),(2,40)},
  {(0,40),(1,16),(2,38)},
  {(0,41),(1,17),(2,36)},
  {(0,42),(1,18),(2,34)},
  {(0,43),(1,19),(2,32)},
  {(0,44),(1,20),(2,30)},
  {(0,45),(1,21),(2,28)},
  {(0,46),(1,22),(2,26)}] : Array (Finset (Fin 3 × ZMod 47)))[i.val]!
  through i := (#[
  [0,47,94,141,188],
  [1,48,95,142,189],
  [2,49,96,143,190],
  [3,50,97,144,191],
  [4,51,98,145,192],
  [5,52,99,146,193],
  [6,53,100,147,194],
  [7,54,101,148,195],
  [8,55,102,149,196],
  [9,56,103,150,197],
  [10,57,104,151,198],
  [11,58,105,152,199],
  [12,59,106,153,200],
  [13,60,107,154,201],
  [14,61,108,155,202],
  [15,62,109,156,203],
  [16,63,110,157,204],
  [17,64,111,158,205],
  [18,65,112,159,206],
  [19,66,113,160,207],
  [20,67,114,161,208],
  [21,68,115,162,209],
  [22,69,116,163,210],
  [23,70,117,164,211],
  [24,71,118,165,212],
  [25,72,119,166,213],
  [26,73,120,167,214],
  [27,74,121,168,215],
  [28,75,122,169,216],
  [29,76,123,170,217],
  [30,77,124,171,218],
  [31,78,125,172,219],
  [32,79,126,173,220],
  [33,80,127,174,221],
  [34,81,128,175,222],
  [35,82,129,176,223],
  [36,83,130,177,224],
  [37,84,131,178,225],
  [38,85,132,179,226],
  [39,86,133,180,227],
  [40,87,134,181,228],
  [41,88,135,182,229],
  [42,89,136,183,230],
  [43,90,137,184,231],
  [44,91,138,185,232],
  [45,92,139,186,233],
  [46,93,140,187,234],
  [0,93,139,177,212],
  [1,47,140,178,213],
  [2,48,94,179,214],
  [3,49,95,180,215],
  [4,50,96,181,216],
  [5,51,97,182,217],
  [6,52,98,183,218],
  [7,53,99,184,219],
  [8,54,100,185,220],
  [9,55,101,186,221],
  [10,56,102,187,222],
  [11,57,103,141,223],
  [12,58,104,142,224],
  [13,59,105,143,225],
  [14,60,106,144,226],
  [15,61,107,145,227],
  [16,62,108,146,228],
  [17,63,109,147,229],
  [18,64,110,148,230],
  [19,65,111,149,231],
  [20,66,112,150,232],
  [21,67,113,151,233],
  [22,68,114,152,234],
  [23,69,115,153,188],
  [24,70,116,154,189],
  [25,71,117,155,190],
  [26,72,118,156,191],
  [27,73,119,157,192],
  [28,74,120,158,193],
  [29,75,121,159,194],
  [30,76,122,160,195],
  [31,77,123,161,196],
  [32,78,124,162,197],
  [33,79,125,163,198],
  [34,80,126,164,199],
  [35,81,127,165,200],
  [36,82,128,166,201],
  [37,83,129,167,202],
  [38,84,130,168,203],
  [39,85,131,169,204],
  [40,86,132,170,205],
  [41,87,133,171,206],
  [42,88,134,172,207],
  [43,89,135,173,208],
  [44,90,136,174,209],
  [45,91,137,175,210],
  [46,92,138,176,211],
  [0,70,140,159,200],
  [23,93,116,182,223],
  [46,69,139,158,199],
  [22,92,115,181,222],
  [45,68,138,157,198],
  [21,91,114,180,221],
  [44,67,137,156,197],
  [20,90,113,179,220],
  [43,66,136,155,196],
  [19,89,112,178,219],
  [42,65,135,154,195],
  [18,88,111,177,218],
  [41,64,134,153,194],
  [17,87,110,176,217],
  [40,63,133,152,193],
  [16,86,109,175,216],
  [39,62,132,151,192],
  [15,85,108,174,215],
  [38,61,131,150,191],
  [14,84,107,173,214],
  [37,60,130,149,190],
  [13,83,106,172,213],
  [36,59,129,148,189],
  [12,82,105,171,212],
  [35,58,128,147,188],
  [11,81,104,170,211],
  [34,57,127,146,234],
  [10,80,103,169,210],
  [33,56,126,145,233],
  [9,79,102,168,209],
  [32,55,125,144,232],
  [8,78,101,167,208],
  [31,54,124,143,231],
  [7,77,100,166,207],
  [30,53,123,142,230],
  [6,76,99,165,206],
  [29,52,122,141,229],
  [5,75,98,164,205],
  [28,51,121,187,228],
  [4,74,97,163,204],
  [27,50,120,186,227],
  [3,73,96,162,203],
  [26,49,119,185,226],
  [2,72,95,161,202],
  [25,48,118,184,225],
  [1,71,94,160,201],
  [24,47,117,183,224]] : Array (List (Fin 235)))[i.val]!
  row i := (#[
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46],
  [47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93],
  [94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140],
  [141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187],
  [188,189,190,191,192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234]] : Array (List (Fin 235)))[i.val]!

def indexShift (r : Fin 5) : ZMod 47 :=
  (#[0,1,2,11,23] : Array (ZMod 47))[r.val]!
def indexRow (i : Fin 235) : Fin 5 := ⟨i.val / 47, by omega⟩
def indexColumn (i : Fin 235) : ZMod 47 := (i.val % 47 : ℕ)

theorem affine_edge_formula : ∀ i, data.edge i = tupleEdge
    (fun j => Supplement.Affine.baseMap (1 : ZMod 47) (indexShift (indexRow i)) j (indexColumn i)) := by
  decide +kernel

theorem index_shift_injective : Function.Injective indexShift := by
  unfold Function.Injective
  decide +kernel

theorem index_parts_injective : Function.Injective (fun i => (indexRow i,indexColumn i)) := by
  intro i j h
  have hd := congrArg (fun x : Fin 5 × ZMod 47 => x.1.val) h
  have hm := congrArg (fun x : Fin 5 × ZMod 47 => x.2.val) h
  change i.val / 47 = j.val / 47 at hd
  have hm' : i.val % 47 = j.val % 47 := by
    simpa [indexColumn,ZMod.val_natCast] using hm
  apply Fin.ext
  omega

theorem table_uniform : ∀ i, (data.edge i).card = 3 := by decide +kernel

theorem table_injective : Function.Injective data.edge := by
  exact affine_table_injective (1 : ZMod 47) indexShift indexRow indexColumn data.edge
    index_shift_injective index_parts_injective affine_edge_formula

theorem table_through_0 : ∀ v : Fin 141,
    0 ≤ v.val → v.val < 8 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_1 : ∀ v : Fin 141,
    8 ≤ v.val → v.val < 16 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_2 : ∀ v : Fin 141,
    16 ≤ v.val → v.val < 24 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_3 : ∀ v : Fin 141,
    24 ≤ v.val → v.val < 32 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_4 : ∀ v : Fin 141,
    32 ≤ v.val → v.val < 40 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_5 : ∀ v : Fin 141,
    40 ≤ v.val → v.val < 48 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_6 : ∀ v : Fin 141,
    48 ≤ v.val → v.val < 56 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_7 : ∀ v : Fin 141,
    56 ≤ v.val → v.val < 64 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_8 : ∀ v : Fin 141,
    64 ≤ v.val → v.val < 72 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_9 : ∀ v : Fin 141,
    72 ≤ v.val → v.val < 80 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_10 : ∀ v : Fin 141,
    80 ≤ v.val → v.val < 88 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_11 : ∀ v : Fin 141,
    88 ≤ v.val → v.val < 96 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_12 : ∀ v : Fin 141,
    96 ≤ v.val → v.val < 104 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_13 : ∀ v : Fin 141,
    104 ≤ v.val → v.val < 112 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_14 : ∀ v : Fin 141,
    112 ≤ v.val → v.val < 120 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_15 : ∀ v : Fin 141,
    120 ≤ v.val → v.val < 128 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_16 : ∀ v : Fin 141,
    128 ≤ v.val → v.val < 136 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through_17 : ∀ v : Fin 141,
    136 ≤ v.val → v.val < 144 →
    ∀ i, data.vertex v ∈ data.edge i → i ∈ data.through v := by decide +kernel

theorem table_through : ∀ v i, data.vertex v ∈ data.edge i → i ∈ data.through v := by
  have checks : ∀ b : Fin 18, ∀ v : Fin 141,
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
    · exact table_through_17
  intro v i hi
  exact checks ⟨v.val/8,by omega⟩ v
    (by change (v.val/8)*8 ≤ v.val; omega)
    (by change v.val < (v.val/8+1)*8; omega) i hi

theorem table_counts_0 : ∀ v : Fin 3 × ZMod 47,
    ((data.row 0).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_1 : ∀ v : Fin 3 × ZMod 47,
    ((data.row 1).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_2 : ∀ v : Fin 3 × ZMod 47,
    ((data.row 2).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_3 : ∀ v : Fin 3 × ZMod 47,
    ((data.row 3).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts_4 : ∀ v : Fin 3 × ZMod 47,
    ((data.row 4).toFinset.filter (fun i => v ∈ data.edge i)).card = 1 := by decide +kernel

theorem table_counts : ∀ r, ∀ v : Fin 3 × ZMod 47,
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

end RigidGHZ.Finite.Seeds.A47
