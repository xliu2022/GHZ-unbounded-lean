module

public import RigidGHZ.Finite.ThreeEdgeCertificate
public import Mathlib.Data.Fin.VecNotation

@[expose] public section
namespace RigidGHZ.Finite

/-- All triples of a nine-element vertex set, in lexicographic order. -/
def nineEdges : Array (Finset (Fin 9)) := #[
  {0,1,2},
  {0,1,3},
  {0,1,4},
  {0,1,5},
  {0,1,6},
  {0,1,7},
  {0,1,8},
  {0,2,3},
  {0,2,4},
  {0,2,5},
  {0,2,6},
  {0,2,7},
  {0,2,8},
  {0,3,4},
  {0,3,5},
  {0,3,6},
  {0,3,7},
  {0,3,8},
  {0,4,5},
  {0,4,6},
  {0,4,7},
  {0,4,8},
  {0,5,6},
  {0,5,7},
  {0,5,8},
  {0,6,7},
  {0,6,8},
  {0,7,8},
  {1,2,3},
  {1,2,4},
  {1,2,5},
  {1,2,6},
  {1,2,7},
  {1,2,8},
  {1,3,4},
  {1,3,5},
  {1,3,6},
  {1,3,7},
  {1,3,8},
  {1,4,5},
  {1,4,6},
  {1,4,7},
  {1,4,8},
  {1,5,6},
  {1,5,7},
  {1,5,8},
  {1,6,7},
  {1,6,8},
  {1,7,8},
  {2,3,4},
  {2,3,5},
  {2,3,6},
  {2,3,7},
  {2,3,8},
  {2,4,5},
  {2,4,6},
  {2,4,7},
  {2,4,8},
  {2,5,6},
  {2,5,7},
  {2,5,8},
  {2,6,7},
  {2,6,8},
  {2,7,8},
  {3,4,5},
  {3,4,6},
  {3,4,7},
  {3,4,8},
  {3,5,6},
  {3,5,7},
  {3,5,8},
  {3,6,7},
  {3,6,8},
  {3,7,8},
  {4,5,6},
  {4,5,7},
  {4,5,8},
  {4,6,7},
  {4,6,8},
  {4,7,8},
  {5,6,7},
  {5,6,8},
  {5,7,8},
  {6,7,8}]

def nineEdge (i : Fin 84) : Finset (Fin 9) := nineEdges[i.val]!

/-- The 280 set partitions of nine vertices into three triples. -/
def ninePartitionCodes : Array (Fin 84 × Fin 84 × Fin 84) := #[
  (0,64,83),
  (0,65,82),
  (0,66,81),
  (0,67,80),
  (0,68,79),
  (0,69,78),
  (0,70,77),
  (0,71,76),
  (0,72,75),
  (0,73,74),
  (1,54,83),
  (1,55,82),
  (1,56,81),
  (1,57,80),
  (1,58,79),
  (1,59,78),
  (1,60,77),
  (1,61,76),
  (1,62,75),
  (1,63,74),
  (2,50,83),
  (2,51,82),
  (2,52,81),
  (2,53,80),
  (2,58,73),
  (2,59,72),
  (2,60,71),
  (2,61,70),
  (2,62,69),
  (2,63,68),
  (3,49,83),
  (3,51,79),
  (3,52,78),
  (3,53,77),
  (3,55,73),
  (3,56,72),
  (3,57,71),
  (3,61,67),
  (3,62,66),
  (3,63,65),
  (4,49,82),
  (4,50,79),
  (4,52,76),
  (4,53,75),
  (4,54,73),
  (4,56,70),
  (4,57,69),
  (4,59,67),
  (4,60,66),
  (4,63,64),
  (5,49,81),
  (5,50,78),
  (5,51,76),
  (5,53,74),
  (5,54,72),
  (5,55,70),
  (5,57,68),
  (5,58,67),
  (5,60,65),
  (5,62,64),
  (6,49,80),
  (6,50,77),
  (6,51,75),
  (6,52,74),
  (6,54,71),
  (6,55,69),
  (6,56,68),
  (6,58,66),
  (6,59,65),
  (6,61,64),
  (7,39,83),
  (7,40,82),
  (7,41,81),
  (7,42,80),
  (7,43,79),
  (7,44,78),
  (7,45,77),
  (7,46,76),
  (7,47,75),
  (7,48,74),
  (8,35,83),
  (8,36,82),
  (8,37,81),
  (8,38,80),
  (8,43,73),
  (8,44,72),
  (8,45,71),
  (8,46,70),
  (8,47,69),
  (8,48,68),
  (9,34,83),
  (9,36,79),
  (9,37,78),
  (9,38,77),
  (9,40,73),
  (9,41,72),
  (9,42,71),
  (9,46,67),
  (9,47,66),
  (9,48,65),
  (10,34,82),
  (10,35,79),
  (10,37,76),
  (10,38,75),
  (10,39,73),
  (10,41,70),
  (10,42,69),
  (10,44,67),
  (10,45,66),
  (10,48,64),
  (11,34,81),
  (11,35,78),
  (11,36,76),
  (11,38,74),
  (11,39,72),
  (11,40,70),
  (11,42,68),
  (11,43,67),
  (11,45,65),
  (11,47,64),
  (12,34,80),
  (12,35,77),
  (12,36,75),
  (12,37,74),
  (12,39,71),
  (12,40,69),
  (12,41,68),
  (12,43,66),
  (12,44,65),
  (12,46,64),
  (13,30,83),
  (13,31,82),
  (13,32,81),
  (13,33,80),
  (13,43,63),
  (13,44,62),
  (13,45,61),
  (13,46,60),
  (13,47,59),
  (13,48,58),
  (14,29,83),
  (14,31,79),
  (14,32,78),
  (14,33,77),
  (14,40,63),
  (14,41,62),
  (14,42,61),
  (14,46,57),
  (14,47,56),
  (14,48,55),
  (15,29,82),
  (15,30,79),
  (15,32,76),
  (15,33,75),
  (15,39,63),
  (15,41,60),
  (15,42,59),
  (15,44,57),
  (15,45,56),
  (15,48,54),
  (16,29,81),
  (16,30,78),
  (16,31,76),
  (16,33,74),
  (16,39,62),
  (16,40,60),
  (16,42,58),
  (16,43,57),
  (16,45,55),
  (16,47,54),
  (17,29,80),
  (17,30,77),
  (17,31,75),
  (17,32,74),
  (17,39,61),
  (17,40,59),
  (17,41,58),
  (17,43,56),
  (17,44,55),
  (17,46,54),
  (18,28,83),
  (18,31,73),
  (18,32,72),
  (18,33,71),
  (18,36,63),
  (18,37,62),
  (18,38,61),
  (18,46,53),
  (18,47,52),
  (18,48,51),
  (19,28,82),
  (19,30,73),
  (19,32,70),
  (19,33,69),
  (19,35,63),
  (19,37,60),
  (19,38,59),
  (19,44,53),
  (19,45,52),
  (19,48,50),
  (20,28,81),
  (20,30,72),
  (20,31,70),
  (20,33,68),
  (20,35,62),
  (20,36,60),
  (20,38,58),
  (20,43,53),
  (20,45,51),
  (20,47,50),
  (21,28,80),
  (21,30,71),
  (21,31,69),
  (21,32,68),
  (21,35,61),
  (21,36,59),
  (21,37,58),
  (21,43,52),
  (21,44,51),
  (21,46,50),
  (22,28,79),
  (22,29,73),
  (22,32,67),
  (22,33,66),
  (22,34,63),
  (22,37,57),
  (22,38,56),
  (22,41,53),
  (22,42,52),
  (22,48,49),
  (23,28,78),
  (23,29,72),
  (23,31,67),
  (23,33,65),
  (23,34,62),
  (23,36,57),
  (23,38,55),
  (23,40,53),
  (23,42,51),
  (23,47,49),
  (24,28,77),
  (24,29,71),
  (24,31,66),
  (24,32,65),
  (24,34,61),
  (24,36,56),
  (24,37,55),
  (24,40,52),
  (24,41,51),
  (24,46,49),
  (25,28,76),
  (25,29,70),
  (25,30,67),
  (25,33,64),
  (25,34,60),
  (25,35,57),
  (25,38,54),
  (25,39,53),
  (25,42,50),
  (25,45,49),
  (26,28,75),
  (26,29,69),
  (26,30,66),
  (26,32,64),
  (26,34,59),
  (26,35,56),
  (26,37,54),
  (26,39,52),
  (26,41,50),
  (26,44,49),
  (27,28,74),
  (27,29,68),
  (27,30,65),
  (27,31,64),
  (27,34,58),
  (27,35,55),
  (27,36,54),
  (27,39,51),
  (27,40,50),
  (27,43,49)]

def ninePartitionCode (i : Fin 280) : Fin 84 × Fin 84 × Fin 84 :=
  ninePartitionCodes[i.val]!

def ninePartition (i : Fin 280) : Hypergraph (Fin 9) :=
  let c := ninePartitionCode i
  {nineEdge c.1, nineEdge c.2.1, nineEdge c.2.2}

/-- Lookup of the partition determined by two disjoint triples. Entries for
intersecting triples are immaterial. -/
def nineCompletionTable : Array (Array (Fin 84 × Fin 280)) := #[
  #[(64,0), (65,1), (66,2), (67,3), (68,4), (69,5), (70,6), (71,7), (72,8), (73,9), (74,9), (75,8), (76,7), (77,6), (78,5), (79,4), (80,3), (81,2), (82,1), (83,0)],
  #[(54,10), (55,11), (56,12), (57,13), (58,14), (59,15), (60,16), (61,17), (62,18), (63,19), (74,19), (75,18), (76,17), (77,16), (78,15), (79,14), (80,13), (81,12), (82,11), (83,10)],
  #[(50,20), (51,21), (52,22), (53,23), (58,24), (59,25), (60,26), (61,27), (62,28), (63,29), (68,29), (69,28), (70,27), (71,26), (72,25), (73,24), (80,23), (81,22), (82,21), (83,20)],
  #[(49,30), (51,31), (52,32), (53,33), (55,34), (56,35), (57,36), (61,37), (62,38), (63,39), (65,39), (66,38), (67,37), (71,36), (72,35), (73,34), (77,33), (78,32), (79,31), (83,30)],
  #[(49,40), (50,41), (52,42), (53,43), (54,44), (56,45), (57,46), (59,47), (60,48), (63,49), (64,49), (66,48), (67,47), (69,46), (70,45), (73,44), (75,43), (76,42), (79,41), (82,40)],
  #[(49,50), (50,51), (51,52), (53,53), (54,54), (55,55), (57,56), (58,57), (60,58), (62,59), (64,59), (65,58), (67,57), (68,56), (70,55), (72,54), (74,53), (76,52), (78,51), (81,50)],
  #[(49,60), (50,61), (51,62), (52,63), (54,64), (55,65), (56,66), (58,67), (59,68), (61,69), (64,69), (65,68), (66,67), (68,66), (69,65), (71,64), (74,63), (75,62), (77,61), (80,60)],
  #[(39,70), (40,71), (41,72), (42,73), (43,74), (44,75), (45,76), (46,77), (47,78), (48,79), (74,79), (75,78), (76,77), (77,76), (78,75), (79,74), (80,73), (81,72), (82,71), (83,70)],
  #[(35,80), (36,81), (37,82), (38,83), (43,84), (44,85), (45,86), (46,87), (47,88), (48,89), (68,89), (69,88), (70,87), (71,86), (72,85), (73,84), (80,83), (81,82), (82,81), (83,80)],
  #[(34,90), (36,91), (37,92), (38,93), (40,94), (41,95), (42,96), (46,97), (47,98), (48,99), (65,99), (66,98), (67,97), (71,96), (72,95), (73,94), (77,93), (78,92), (79,91), (83,90)],
  #[(34,100), (35,101), (37,102), (38,103), (39,104), (41,105), (42,106), (44,107), (45,108), (48,109), (64,109), (66,108), (67,107), (69,106), (70,105), (73,104), (75,103), (76,102), (79,101), (82,100)],
  #[(34,110), (35,111), (36,112), (38,113), (39,114), (40,115), (42,116), (43,117), (45,118), (47,119), (64,119), (65,118), (67,117), (68,116), (70,115), (72,114), (74,113), (76,112), (78,111), (81,110)],
  #[(34,120), (35,121), (36,122), (37,123), (39,124), (40,125), (41,126), (43,127), (44,128), (46,129), (64,129), (65,128), (66,127), (68,126), (69,125), (71,124), (74,123), (75,122), (77,121), (80,120)],
  #[(30,130), (31,131), (32,132), (33,133), (43,134), (44,135), (45,136), (46,137), (47,138), (48,139), (58,139), (59,138), (60,137), (61,136), (62,135), (63,134), (80,133), (81,132), (82,131), (83,130)],
  #[(29,140), (31,141), (32,142), (33,143), (40,144), (41,145), (42,146), (46,147), (47,148), (48,149), (55,149), (56,148), (57,147), (61,146), (62,145), (63,144), (77,143), (78,142), (79,141), (83,140)],
  #[(29,150), (30,151), (32,152), (33,153), (39,154), (41,155), (42,156), (44,157), (45,158), (48,159), (54,159), (56,158), (57,157), (59,156), (60,155), (63,154), (75,153), (76,152), (79,151), (82,150)],
  #[(29,160), (30,161), (31,162), (33,163), (39,164), (40,165), (42,166), (43,167), (45,168), (47,169), (54,169), (55,168), (57,167), (58,166), (60,165), (62,164), (74,163), (76,162), (78,161), (81,160)],
  #[(29,170), (30,171), (31,172), (32,173), (39,174), (40,175), (41,176), (43,177), (44,178), (46,179), (54,179), (55,178), (56,177), (58,176), (59,175), (61,174), (74,173), (75,172), (77,171), (80,170)],
  #[(28,180), (31,181), (32,182), (33,183), (36,184), (37,185), (38,186), (46,187), (47,188), (48,189), (51,189), (52,188), (53,187), (61,186), (62,185), (63,184), (71,183), (72,182), (73,181), (83,180)],
  #[(28,190), (30,191), (32,192), (33,193), (35,194), (37,195), (38,196), (44,197), (45,198), (48,199), (50,199), (52,198), (53,197), (59,196), (60,195), (63,194), (69,193), (70,192), (73,191), (82,190)],
  #[(28,200), (30,201), (31,202), (33,203), (35,204), (36,205), (38,206), (43,207), (45,208), (47,209), (50,209), (51,208), (53,207), (58,206), (60,205), (62,204), (68,203), (70,202), (72,201), (81,200)],
  #[(28,210), (30,211), (31,212), (32,213), (35,214), (36,215), (37,216), (43,217), (44,218), (46,219), (50,219), (51,218), (52,217), (58,216), (59,215), (61,214), (68,213), (69,212), (71,211), (80,210)],
  #[(28,220), (29,221), (32,222), (33,223), (34,224), (37,225), (38,226), (41,227), (42,228), (48,229), (49,229), (52,228), (53,227), (56,226), (57,225), (63,224), (66,223), (67,222), (73,221), (79,220)],
  #[(28,230), (29,231), (31,232), (33,233), (34,234), (36,235), (38,236), (40,237), (42,238), (47,239), (49,239), (51,238), (53,237), (55,236), (57,235), (62,234), (65,233), (67,232), (72,231), (78,230)],
  #[(28,240), (29,241), (31,242), (32,243), (34,244), (36,245), (37,246), (40,247), (41,248), (46,249), (49,249), (51,248), (52,247), (55,246), (56,245), (61,244), (65,243), (66,242), (71,241), (77,240)],
  #[(28,250), (29,251), (30,252), (33,253), (34,254), (35,255), (38,256), (39,257), (42,258), (45,259), (49,259), (50,258), (53,257), (54,256), (57,255), (60,254), (64,253), (67,252), (70,251), (76,250)],
  #[(28,260), (29,261), (30,262), (32,263), (34,264), (35,265), (37,266), (39,267), (41,268), (44,269), (49,269), (50,268), (52,267), (54,266), (56,265), (59,264), (64,263), (66,262), (69,261), (75,260)],
  #[(28,270), (29,271), (30,272), (31,273), (34,274), (35,275), (36,276), (39,277), (40,278), (43,279), (49,279), (50,278), (51,277), (54,276), (55,275), (58,274), (64,273), (65,272), (68,271), (74,270)],
  #[(18,180), (19,190), (20,200), (21,210), (22,220), (23,230), (24,240), (25,250), (26,260), (27,270), (74,270), (75,260), (76,250), (77,240), (78,230), (79,220), (80,210), (81,200), (82,190), (83,180)],
  #[(14,140), (15,150), (16,160), (17,170), (22,221), (23,231), (24,241), (25,251), (26,261), (27,271), (68,271), (69,261), (70,251), (71,241), (72,231), (73,221), (80,170), (81,160), (82,150), (83,140)],
  #[(13,130), (15,151), (16,161), (17,171), (19,191), (20,201), (21,211), (25,252), (26,262), (27,272), (65,272), (66,262), (67,252), (71,211), (72,201), (73,191), (77,171), (78,161), (79,151), (83,130)],
  #[(13,131), (14,141), (16,162), (17,172), (18,181), (20,202), (21,212), (23,232), (24,242), (27,273), (64,273), (66,242), (67,232), (69,212), (70,202), (73,181), (75,172), (76,162), (79,141), (82,131)],
  #[(13,132), (14,142), (15,152), (17,173), (18,182), (19,192), (21,213), (22,222), (24,243), (26,263), (64,263), (65,243), (67,222), (68,213), (70,192), (72,182), (74,173), (76,152), (78,142), (81,132)],
  #[(13,133), (14,143), (15,153), (16,163), (18,183), (19,193), (20,203), (22,223), (23,233), (25,253), (64,253), (65,233), (66,223), (68,203), (69,193), (71,183), (74,163), (75,153), (77,143), (80,133)],
  #[(9,90), (10,100), (11,110), (12,120), (22,224), (23,234), (24,244), (25,254), (26,264), (27,274), (58,274), (59,264), (60,254), (61,244), (62,234), (63,224), (80,120), (81,110), (82,100), (83,90)],
  #[(8,80), (10,101), (11,111), (12,121), (19,194), (20,204), (21,214), (25,255), (26,265), (27,275), (55,275), (56,265), (57,255), (61,214), (62,204), (63,194), (77,121), (78,111), (79,101), (83,80)],
  #[(8,81), (9,91), (11,112), (12,122), (18,184), (20,205), (21,215), (23,235), (24,245), (27,276), (54,276), (56,245), (57,235), (59,215), (60,205), (63,184), (75,122), (76,112), (79,91), (82,81)],
  #[(8,82), (9,92), (10,102), (12,123), (18,185), (19,195), (21,216), (22,225), (24,246), (26,266), (54,266), (55,246), (57,225), (58,216), (60,195), (62,185), (74,123), (76,102), (78,92), (81,82)],
  #[(8,83), (9,93), (10,103), (11,113), (18,186), (19,196), (20,206), (22,226), (23,236), (25,256), (54,256), (55,236), (56,226), (58,206), (59,196), (61,186), (74,113), (75,103), (77,93), (80,83)],
  #[(7,70), (10,104), (11,114), (12,124), (15,154), (16,164), (17,174), (25,257), (26,267), (27,277), (51,277), (52,267), (53,257), (61,174), (62,164), (63,154), (71,124), (72,114), (73,104), (83,70)],
  #[(7,71), (9,94), (11,115), (12,125), (14,144), (16,165), (17,175), (23,237), (24,247), (27,278), (50,278), (52,247), (53,237), (59,175), (60,165), (63,144), (69,125), (70,115), (73,94), (82,71)],
  #[(7,72), (9,95), (10,105), (12,126), (14,145), (15,155), (17,176), (22,227), (24,248), (26,268), (50,268), (51,248), (53,227), (58,176), (60,155), (62,145), (68,126), (70,105), (72,95), (81,72)],
  #[(7,73), (9,96), (10,106), (11,116), (14,146), (15,156), (16,166), (22,228), (23,238), (25,258), (50,258), (51,238), (52,228), (58,166), (59,156), (61,146), (68,116), (69,106), (71,96), (80,73)],
  #[(7,74), (8,84), (11,117), (12,127), (13,134), (16,167), (17,177), (20,207), (21,217), (27,279), (49,279), (52,217), (53,207), (56,177), (57,167), (63,134), (66,127), (67,117), (73,84), (79,74)],
  #[(7,75), (8,85), (10,107), (12,128), (13,135), (15,157), (17,178), (19,197), (21,218), (26,269), (49,269), (51,218), (53,197), (55,178), (57,157), (62,135), (65,128), (67,107), (72,85), (78,75)],
  #[(7,76), (8,86), (10,108), (11,118), (13,136), (15,158), (16,168), (19,198), (20,208), (25,259), (49,259), (51,208), (52,198), (55,168), (56,158), (61,136), (65,118), (66,108), (71,86), (77,76)],
  #[(7,77), (8,87), (9,97), (12,129), (13,137), (14,147), (17,179), (18,187), (21,219), (24,249), (49,249), (50,219), (53,187), (54,179), (57,147), (60,137), (64,129), (67,97), (70,87), (76,77)],
  #[(7,78), (8,88), (9,98), (11,119), (13,138), (14,148), (16,169), (18,188), (20,209), (23,239), (49,239), (50,209), (52,188), (54,169), (56,148), (59,138), (64,119), (66,98), (69,88), (75,78)],
  #[(7,79), (8,89), (9,99), (10,109), (13,139), (14,149), (15,159), (18,189), (19,199), (22,229), (49,229), (50,199), (51,189), (54,159), (55,149), (58,139), (64,109), (65,99), (68,89), (74,79)],
  #[(3,30), (4,40), (5,50), (6,60), (22,229), (23,239), (24,249), (25,259), (26,269), (27,279), (43,279), (44,269), (45,259), (46,249), (47,239), (48,229), (80,60), (81,50), (82,40), (83,30)],
  #[(2,20), (4,41), (5,51), (6,61), (19,199), (20,209), (21,219), (25,258), (26,268), (27,278), (40,278), (41,268), (42,258), (46,219), (47,209), (48,199), (77,61), (78,51), (79,41), (83,20)],
  #[(2,21), (3,31), (5,52), (6,62), (18,189), (20,208), (21,218), (23,238), (24,248), (27,277), (39,277), (41,248), (42,238), (44,218), (45,208), (48,189), (75,62), (76,52), (79,31), (82,21)],
  #[(2,22), (3,32), (4,42), (6,63), (18,188), (19,198), (21,217), (22,228), (24,247), (26,267), (39,267), (40,247), (42,228), (43,217), (45,198), (47,188), (74,63), (76,42), (78,32), (81,22)],
  #[(2,23), (3,33), (4,43), (5,53), (18,187), (19,197), (20,207), (22,227), (23,237), (25,257), (39,257), (40,237), (41,227), (43,207), (44,197), (46,187), (74,53), (75,43), (77,33), (80,23)],
  #[(1,10), (4,44), (5,54), (6,64), (15,159), (16,169), (17,179), (25,256), (26,266), (27,276), (36,276), (37,266), (38,256), (46,179), (47,169), (48,159), (71,64), (72,54), (73,44), (83,10)],
  #[(1,11), (3,34), (5,55), (6,65), (14,149), (16,168), (17,178), (23,236), (24,246), (27,275), (35,275), (37,246), (38,236), (44,178), (45,168), (48,149), (69,65), (70,55), (73,34), (82,11)],
  #[(1,12), (3,35), (4,45), (6,66), (14,148), (15,158), (17,177), (22,226), (24,245), (26,265), (35,265), (36,245), (38,226), (43,177), (45,158), (47,148), (68,66), (70,45), (72,35), (81,12)],
  #[(1,13), (3,36), (4,46), (5,56), (14,147), (15,157), (16,167), (22,225), (23,235), (25,255), (35,255), (36,235), (37,225), (43,167), (44,157), (46,147), (68,56), (69,46), (71,36), (80,13)],
  #[(1,14), (2,24), (5,57), (6,67), (13,139), (16,166), (17,176), (20,206), (21,216), (27,274), (34,274), (37,216), (38,206), (41,176), (42,166), (48,139), (66,67), (67,57), (73,24), (79,14)],
  #[(1,15), (2,25), (4,47), (6,68), (13,138), (15,156), (17,175), (19,196), (21,215), (26,264), (34,264), (36,215), (38,196), (40,175), (42,156), (47,138), (65,68), (67,47), (72,25), (78,15)],
  #[(1,16), (2,26), (4,48), (5,58), (13,137), (15,155), (16,165), (19,195), (20,205), (25,254), (34,254), (36,205), (37,195), (40,165), (41,155), (46,137), (65,58), (66,48), (71,26), (77,16)],
  #[(1,17), (2,27), (3,37), (6,69), (13,136), (14,146), (17,174), (18,186), (21,214), (24,244), (34,244), (35,214), (38,186), (39,174), (42,146), (45,136), (64,69), (67,37), (70,27), (76,17)],
  #[(1,18), (2,28), (3,38), (5,59), (13,135), (14,145), (16,164), (18,185), (20,204), (23,234), (34,234), (35,204), (37,185), (39,164), (41,145), (44,135), (64,59), (66,38), (69,28), (75,18)],
  #[(1,19), (2,29), (3,39), (4,49), (13,134), (14,144), (15,154), (18,184), (19,194), (22,224), (34,224), (35,194), (36,184), (39,154), (40,144), (43,134), (64,49), (65,39), (68,29), (74,19)],
  #[(0,0), (4,49), (5,59), (6,69), (10,109), (11,119), (12,129), (25,253), (26,263), (27,273), (31,273), (32,263), (33,253), (46,129), (47,119), (48,109), (61,69), (62,59), (63,49), (83,0)],
  #[(0,1), (3,39), (5,58), (6,68), (9,99), (11,118), (12,128), (23,233), (24,243), (27,272), (30,272), (32,243), (33,233), (44,128), (45,118), (48,99), (59,68), (60,58), (63,39), (82,1)],
  #[(0,2), (3,38), (4,48), (6,67), (9,98), (10,108), (12,127), (22,223), (24,242), (26,262), (30,262), (31,242), (33,223), (43,127), (45,108), (47,98), (58,67), (60,48), (62,38), (81,2)],
  #[(0,3), (3,37), (4,47), (5,57), (9,97), (10,107), (11,117), (22,222), (23,232), (25,252), (30,252), (31,232), (32,222), (43,117), (44,107), (46,97), (58,57), (59,47), (61,37), (80,3)],
  #[(0,4), (2,29), (5,56), (6,66), (8,89), (11,116), (12,126), (20,203), (21,213), (27,271), (29,271), (32,213), (33,203), (41,126), (42,116), (48,89), (56,66), (57,56), (63,29), (79,4)],
  #[(0,5), (2,28), (4,46), (6,65), (8,88), (10,106), (12,125), (19,193), (21,212), (26,261), (29,261), (31,212), (33,193), (40,125), (42,106), (47,88), (55,65), (57,46), (62,28), (78,5)],
  #[(0,6), (2,27), (4,45), (5,55), (8,87), (10,105), (11,115), (19,192), (20,202), (25,251), (29,251), (31,202), (32,192), (40,115), (41,105), (46,87), (55,55), (56,45), (61,27), (77,6)],
  #[(0,7), (2,26), (3,36), (6,64), (8,86), (9,96), (12,124), (18,183), (21,211), (24,241), (29,241), (30,211), (33,183), (39,124), (42,96), (45,86), (54,64), (57,36), (60,26), (76,7)],
  #[(0,8), (2,25), (3,35), (5,54), (8,85), (9,95), (11,114), (18,182), (20,201), (23,231), (29,231), (30,201), (32,182), (39,114), (41,95), (44,85), (54,54), (56,35), (59,25), (75,8)],
  #[(0,9), (2,24), (3,34), (4,44), (8,84), (9,94), (10,104), (18,181), (19,191), (22,221), (29,221), (30,191), (31,181), (39,104), (40,94), (43,84), (54,44), (55,34), (58,24), (74,9)],
  #[(0,9), (1,19), (5,53), (6,63), (7,79), (11,113), (12,123), (16,163), (17,173), (27,270), (28,270), (32,173), (33,163), (37,123), (38,113), (48,79), (52,63), (53,53), (63,19), (73,9)],
  #[(0,8), (1,18), (4,43), (6,62), (7,78), (10,103), (12,122), (15,153), (17,172), (26,260), (28,260), (31,172), (33,153), (36,122), (38,103), (47,78), (51,62), (53,43), (62,18), (72,8)],
  #[(0,7), (1,17), (4,42), (5,52), (7,77), (10,102), (11,112), (15,152), (16,162), (25,250), (28,250), (31,162), (32,152), (36,112), (37,102), (46,77), (51,52), (52,42), (61,17), (71,7)],
  #[(0,6), (1,16), (3,33), (6,61), (7,76), (9,93), (12,121), (14,143), (17,171), (24,240), (28,240), (30,171), (33,143), (35,121), (38,93), (45,76), (50,61), (53,33), (60,16), (70,6)],
  #[(0,5), (1,15), (3,32), (5,51), (7,75), (9,92), (11,111), (14,142), (16,161), (23,230), (28,230), (30,161), (32,142), (35,111), (37,92), (44,75), (50,51), (52,32), (59,15), (69,5)],
  #[(0,4), (1,14), (3,31), (4,41), (7,74), (9,91), (10,101), (14,141), (15,151), (22,220), (28,220), (30,151), (31,141), (35,101), (36,91), (43,74), (50,41), (51,31), (58,14), (68,4)],
  #[(0,3), (1,13), (2,23), (6,60), (7,73), (8,83), (12,120), (13,133), (17,170), (21,210), (28,210), (29,170), (33,133), (34,120), (38,83), (42,73), (49,60), (53,23), (57,13), (67,3)],
  #[(0,2), (1,12), (2,22), (5,50), (7,72), (8,82), (11,110), (13,132), (16,160), (20,200), (28,200), (29,160), (32,132), (34,110), (37,82), (41,72), (49,50), (52,22), (56,12), (66,2)],
  #[(0,1), (1,11), (2,21), (4,40), (7,71), (8,81), (10,100), (13,131), (15,150), (19,190), (28,190), (29,150), (31,131), (34,100), (36,81), (40,71), (49,40), (51,21), (55,11), (65,1)],
  #[(0,0), (1,10), (2,20), (3,30), (7,70), (8,80), (9,90), (13,130), (14,140), (18,180), (28,180), (29,140), (30,130), (34,90), (35,80), (39,70), (49,30), (50,20), (54,10), (64,0)]]

def nineCompletion (i j : Fin 84) : Fin 280 :=
  (((nineCompletionTable[i.val]!).toList.find? (fun p => p.1 = j)).map Prod.snd).getD 0

set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000


 theorem nineEdge_card (i : Fin 84) : (nineEdge i).card = 3 := by
  have hcheck : (List.finRange 84).all (fun i => decide ((nineEdge i).card = 3)) = true := by decide +kernel
  have h : ∀ i : Fin 84, (nineEdge i).card = 3 := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using hcheck
  exact h i


 theorem nineEdge_injective : Function.Injective nineEdge := by
  have hcheck : (List.finRange 84).all (fun i => (List.finRange 84).all
    (fun j => decide (nineEdge i = nineEdge j → i = j))) = true := by decide +kernel
  simpa only [Function.Injective, List.all_eq_true, List.mem_finRange, true_implies,
    decide_eq_true_eq] using hcheck


 theorem nineEdge_complete (e : Finset (Fin 9)) (he : e.card = 3) :
    ∃ i : Fin 84, nineEdge i = e := by
  have hc : (List.finRange 9).all (fun a => (List.finRange 9).all (fun b =>
      (List.finRange 9).all (fun c => decide (a ≠ b → a ≠ c → b ≠ c →
        ∃ i : Fin 84, nineEdge i = {a,b,c})))) = true := by decide +kernel
  have h : ∀ a b c : Fin 9, a ≠ b → a ≠ c → b ≠ c →
      ∃ i : Fin 84, nineEdge i = {a,b,c} := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp he
  exact h a b c hab hac hbc


local instance ninePerfectMatchingDecidable (H M : Hypergraph (Fin 9)) :
    Decidable (PerfectMatching H M) := by unfold PerfectMatching; infer_instance

 theorem ninePartition_perfect (i : Fin 280) :
    PerfectMatching (ninePartition i) (ninePartition i) := by
  have hcheck : (List.finRange 280).all
      (fun i => decide (PerfectMatching (ninePartition i) (ninePartition i))) = true := by decide +kernel
  have h : ∀ i : Fin 280, PerfectMatching (ninePartition i) (ninePartition i) := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using hcheck
  exact h i


 theorem nineCompletion_correct_0 (j : Fin 84) (h : Disjoint (nineEdge 0) (nineEdge j)) :
    {nineEdge 0,nineEdge j,Finset.univ \ (nineEdge 0 ∪ nineEdge j)} =
      ninePartition (nineCompletion 0 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 0) (nineEdge j) →
    {nineEdge 0,nineEdge j,Finset.univ \ (nineEdge 0 ∪ nineEdge j)} =
      ninePartition (nineCompletion 0 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 0) (nineEdge j) →
    {nineEdge 0,nineEdge j,Finset.univ \ (nineEdge 0 ∪ nineEdge j)} =
      ninePartition (nineCompletion 0 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_1 (j : Fin 84) (h : Disjoint (nineEdge 1) (nineEdge j)) :
    {nineEdge 1,nineEdge j,Finset.univ \ (nineEdge 1 ∪ nineEdge j)} =
      ninePartition (nineCompletion 1 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 1) (nineEdge j) →
    {nineEdge 1,nineEdge j,Finset.univ \ (nineEdge 1 ∪ nineEdge j)} =
      ninePartition (nineCompletion 1 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 1) (nineEdge j) →
    {nineEdge 1,nineEdge j,Finset.univ \ (nineEdge 1 ∪ nineEdge j)} =
      ninePartition (nineCompletion 1 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_2 (j : Fin 84) (h : Disjoint (nineEdge 2) (nineEdge j)) :
    {nineEdge 2,nineEdge j,Finset.univ \ (nineEdge 2 ∪ nineEdge j)} =
      ninePartition (nineCompletion 2 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 2) (nineEdge j) →
    {nineEdge 2,nineEdge j,Finset.univ \ (nineEdge 2 ∪ nineEdge j)} =
      ninePartition (nineCompletion 2 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 2) (nineEdge j) →
    {nineEdge 2,nineEdge j,Finset.univ \ (nineEdge 2 ∪ nineEdge j)} =
      ninePartition (nineCompletion 2 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_3 (j : Fin 84) (h : Disjoint (nineEdge 3) (nineEdge j)) :
    {nineEdge 3,nineEdge j,Finset.univ \ (nineEdge 3 ∪ nineEdge j)} =
      ninePartition (nineCompletion 3 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 3) (nineEdge j) →
    {nineEdge 3,nineEdge j,Finset.univ \ (nineEdge 3 ∪ nineEdge j)} =
      ninePartition (nineCompletion 3 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 3) (nineEdge j) →
    {nineEdge 3,nineEdge j,Finset.univ \ (nineEdge 3 ∪ nineEdge j)} =
      ninePartition (nineCompletion 3 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_4 (j : Fin 84) (h : Disjoint (nineEdge 4) (nineEdge j)) :
    {nineEdge 4,nineEdge j,Finset.univ \ (nineEdge 4 ∪ nineEdge j)} =
      ninePartition (nineCompletion 4 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 4) (nineEdge j) →
    {nineEdge 4,nineEdge j,Finset.univ \ (nineEdge 4 ∪ nineEdge j)} =
      ninePartition (nineCompletion 4 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 4) (nineEdge j) →
    {nineEdge 4,nineEdge j,Finset.univ \ (nineEdge 4 ∪ nineEdge j)} =
      ninePartition (nineCompletion 4 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_5 (j : Fin 84) (h : Disjoint (nineEdge 5) (nineEdge j)) :
    {nineEdge 5,nineEdge j,Finset.univ \ (nineEdge 5 ∪ nineEdge j)} =
      ninePartition (nineCompletion 5 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 5) (nineEdge j) →
    {nineEdge 5,nineEdge j,Finset.univ \ (nineEdge 5 ∪ nineEdge j)} =
      ninePartition (nineCompletion 5 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 5) (nineEdge j) →
    {nineEdge 5,nineEdge j,Finset.univ \ (nineEdge 5 ∪ nineEdge j)} =
      ninePartition (nineCompletion 5 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_6 (j : Fin 84) (h : Disjoint (nineEdge 6) (nineEdge j)) :
    {nineEdge 6,nineEdge j,Finset.univ \ (nineEdge 6 ∪ nineEdge j)} =
      ninePartition (nineCompletion 6 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 6) (nineEdge j) →
    {nineEdge 6,nineEdge j,Finset.univ \ (nineEdge 6 ∪ nineEdge j)} =
      ninePartition (nineCompletion 6 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 6) (nineEdge j) →
    {nineEdge 6,nineEdge j,Finset.univ \ (nineEdge 6 ∪ nineEdge j)} =
      ninePartition (nineCompletion 6 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_7 (j : Fin 84) (h : Disjoint (nineEdge 7) (nineEdge j)) :
    {nineEdge 7,nineEdge j,Finset.univ \ (nineEdge 7 ∪ nineEdge j)} =
      ninePartition (nineCompletion 7 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 7) (nineEdge j) →
    {nineEdge 7,nineEdge j,Finset.univ \ (nineEdge 7 ∪ nineEdge j)} =
      ninePartition (nineCompletion 7 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 7) (nineEdge j) →
    {nineEdge 7,nineEdge j,Finset.univ \ (nineEdge 7 ∪ nineEdge j)} =
      ninePartition (nineCompletion 7 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_8 (j : Fin 84) (h : Disjoint (nineEdge 8) (nineEdge j)) :
    {nineEdge 8,nineEdge j,Finset.univ \ (nineEdge 8 ∪ nineEdge j)} =
      ninePartition (nineCompletion 8 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 8) (nineEdge j) →
    {nineEdge 8,nineEdge j,Finset.univ \ (nineEdge 8 ∪ nineEdge j)} =
      ninePartition (nineCompletion 8 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 8) (nineEdge j) →
    {nineEdge 8,nineEdge j,Finset.univ \ (nineEdge 8 ∪ nineEdge j)} =
      ninePartition (nineCompletion 8 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_9 (j : Fin 84) (h : Disjoint (nineEdge 9) (nineEdge j)) :
    {nineEdge 9,nineEdge j,Finset.univ \ (nineEdge 9 ∪ nineEdge j)} =
      ninePartition (nineCompletion 9 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 9) (nineEdge j) →
    {nineEdge 9,nineEdge j,Finset.univ \ (nineEdge 9 ∪ nineEdge j)} =
      ninePartition (nineCompletion 9 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 9) (nineEdge j) →
    {nineEdge 9,nineEdge j,Finset.univ \ (nineEdge 9 ∪ nineEdge j)} =
      ninePartition (nineCompletion 9 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_10 (j : Fin 84) (h : Disjoint (nineEdge 10) (nineEdge j)) :
    {nineEdge 10,nineEdge j,Finset.univ \ (nineEdge 10 ∪ nineEdge j)} =
      ninePartition (nineCompletion 10 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 10) (nineEdge j) →
    {nineEdge 10,nineEdge j,Finset.univ \ (nineEdge 10 ∪ nineEdge j)} =
      ninePartition (nineCompletion 10 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 10) (nineEdge j) →
    {nineEdge 10,nineEdge j,Finset.univ \ (nineEdge 10 ∪ nineEdge j)} =
      ninePartition (nineCompletion 10 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_11 (j : Fin 84) (h : Disjoint (nineEdge 11) (nineEdge j)) :
    {nineEdge 11,nineEdge j,Finset.univ \ (nineEdge 11 ∪ nineEdge j)} =
      ninePartition (nineCompletion 11 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 11) (nineEdge j) →
    {nineEdge 11,nineEdge j,Finset.univ \ (nineEdge 11 ∪ nineEdge j)} =
      ninePartition (nineCompletion 11 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 11) (nineEdge j) →
    {nineEdge 11,nineEdge j,Finset.univ \ (nineEdge 11 ∪ nineEdge j)} =
      ninePartition (nineCompletion 11 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_12 (j : Fin 84) (h : Disjoint (nineEdge 12) (nineEdge j)) :
    {nineEdge 12,nineEdge j,Finset.univ \ (nineEdge 12 ∪ nineEdge j)} =
      ninePartition (nineCompletion 12 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 12) (nineEdge j) →
    {nineEdge 12,nineEdge j,Finset.univ \ (nineEdge 12 ∪ nineEdge j)} =
      ninePartition (nineCompletion 12 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 12) (nineEdge j) →
    {nineEdge 12,nineEdge j,Finset.univ \ (nineEdge 12 ∪ nineEdge j)} =
      ninePartition (nineCompletion 12 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_13 (j : Fin 84) (h : Disjoint (nineEdge 13) (nineEdge j)) :
    {nineEdge 13,nineEdge j,Finset.univ \ (nineEdge 13 ∪ nineEdge j)} =
      ninePartition (nineCompletion 13 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 13) (nineEdge j) →
    {nineEdge 13,nineEdge j,Finset.univ \ (nineEdge 13 ∪ nineEdge j)} =
      ninePartition (nineCompletion 13 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 13) (nineEdge j) →
    {nineEdge 13,nineEdge j,Finset.univ \ (nineEdge 13 ∪ nineEdge j)} =
      ninePartition (nineCompletion 13 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_14 (j : Fin 84) (h : Disjoint (nineEdge 14) (nineEdge j)) :
    {nineEdge 14,nineEdge j,Finset.univ \ (nineEdge 14 ∪ nineEdge j)} =
      ninePartition (nineCompletion 14 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 14) (nineEdge j) →
    {nineEdge 14,nineEdge j,Finset.univ \ (nineEdge 14 ∪ nineEdge j)} =
      ninePartition (nineCompletion 14 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 14) (nineEdge j) →
    {nineEdge 14,nineEdge j,Finset.univ \ (nineEdge 14 ∪ nineEdge j)} =
      ninePartition (nineCompletion 14 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_15 (j : Fin 84) (h : Disjoint (nineEdge 15) (nineEdge j)) :
    {nineEdge 15,nineEdge j,Finset.univ \ (nineEdge 15 ∪ nineEdge j)} =
      ninePartition (nineCompletion 15 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 15) (nineEdge j) →
    {nineEdge 15,nineEdge j,Finset.univ \ (nineEdge 15 ∪ nineEdge j)} =
      ninePartition (nineCompletion 15 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 15) (nineEdge j) →
    {nineEdge 15,nineEdge j,Finset.univ \ (nineEdge 15 ∪ nineEdge j)} =
      ninePartition (nineCompletion 15 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_16 (j : Fin 84) (h : Disjoint (nineEdge 16) (nineEdge j)) :
    {nineEdge 16,nineEdge j,Finset.univ \ (nineEdge 16 ∪ nineEdge j)} =
      ninePartition (nineCompletion 16 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 16) (nineEdge j) →
    {nineEdge 16,nineEdge j,Finset.univ \ (nineEdge 16 ∪ nineEdge j)} =
      ninePartition (nineCompletion 16 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 16) (nineEdge j) →
    {nineEdge 16,nineEdge j,Finset.univ \ (nineEdge 16 ∪ nineEdge j)} =
      ninePartition (nineCompletion 16 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_17 (j : Fin 84) (h : Disjoint (nineEdge 17) (nineEdge j)) :
    {nineEdge 17,nineEdge j,Finset.univ \ (nineEdge 17 ∪ nineEdge j)} =
      ninePartition (nineCompletion 17 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 17) (nineEdge j) →
    {nineEdge 17,nineEdge j,Finset.univ \ (nineEdge 17 ∪ nineEdge j)} =
      ninePartition (nineCompletion 17 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 17) (nineEdge j) →
    {nineEdge 17,nineEdge j,Finset.univ \ (nineEdge 17 ∪ nineEdge j)} =
      ninePartition (nineCompletion 17 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_18 (j : Fin 84) (h : Disjoint (nineEdge 18) (nineEdge j)) :
    {nineEdge 18,nineEdge j,Finset.univ \ (nineEdge 18 ∪ nineEdge j)} =
      ninePartition (nineCompletion 18 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 18) (nineEdge j) →
    {nineEdge 18,nineEdge j,Finset.univ \ (nineEdge 18 ∪ nineEdge j)} =
      ninePartition (nineCompletion 18 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 18) (nineEdge j) →
    {nineEdge 18,nineEdge j,Finset.univ \ (nineEdge 18 ∪ nineEdge j)} =
      ninePartition (nineCompletion 18 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_19 (j : Fin 84) (h : Disjoint (nineEdge 19) (nineEdge j)) :
    {nineEdge 19,nineEdge j,Finset.univ \ (nineEdge 19 ∪ nineEdge j)} =
      ninePartition (nineCompletion 19 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 19) (nineEdge j) →
    {nineEdge 19,nineEdge j,Finset.univ \ (nineEdge 19 ∪ nineEdge j)} =
      ninePartition (nineCompletion 19 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 19) (nineEdge j) →
    {nineEdge 19,nineEdge j,Finset.univ \ (nineEdge 19 ∪ nineEdge j)} =
      ninePartition (nineCompletion 19 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_20 (j : Fin 84) (h : Disjoint (nineEdge 20) (nineEdge j)) :
    {nineEdge 20,nineEdge j,Finset.univ \ (nineEdge 20 ∪ nineEdge j)} =
      ninePartition (nineCompletion 20 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 20) (nineEdge j) →
    {nineEdge 20,nineEdge j,Finset.univ \ (nineEdge 20 ∪ nineEdge j)} =
      ninePartition (nineCompletion 20 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 20) (nineEdge j) →
    {nineEdge 20,nineEdge j,Finset.univ \ (nineEdge 20 ∪ nineEdge j)} =
      ninePartition (nineCompletion 20 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_21 (j : Fin 84) (h : Disjoint (nineEdge 21) (nineEdge j)) :
    {nineEdge 21,nineEdge j,Finset.univ \ (nineEdge 21 ∪ nineEdge j)} =
      ninePartition (nineCompletion 21 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 21) (nineEdge j) →
    {nineEdge 21,nineEdge j,Finset.univ \ (nineEdge 21 ∪ nineEdge j)} =
      ninePartition (nineCompletion 21 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 21) (nineEdge j) →
    {nineEdge 21,nineEdge j,Finset.univ \ (nineEdge 21 ∪ nineEdge j)} =
      ninePartition (nineCompletion 21 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_22 (j : Fin 84) (h : Disjoint (nineEdge 22) (nineEdge j)) :
    {nineEdge 22,nineEdge j,Finset.univ \ (nineEdge 22 ∪ nineEdge j)} =
      ninePartition (nineCompletion 22 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 22) (nineEdge j) →
    {nineEdge 22,nineEdge j,Finset.univ \ (nineEdge 22 ∪ nineEdge j)} =
      ninePartition (nineCompletion 22 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 22) (nineEdge j) →
    {nineEdge 22,nineEdge j,Finset.univ \ (nineEdge 22 ∪ nineEdge j)} =
      ninePartition (nineCompletion 22 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_23 (j : Fin 84) (h : Disjoint (nineEdge 23) (nineEdge j)) :
    {nineEdge 23,nineEdge j,Finset.univ \ (nineEdge 23 ∪ nineEdge j)} =
      ninePartition (nineCompletion 23 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 23) (nineEdge j) →
    {nineEdge 23,nineEdge j,Finset.univ \ (nineEdge 23 ∪ nineEdge j)} =
      ninePartition (nineCompletion 23 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 23) (nineEdge j) →
    {nineEdge 23,nineEdge j,Finset.univ \ (nineEdge 23 ∪ nineEdge j)} =
      ninePartition (nineCompletion 23 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_24 (j : Fin 84) (h : Disjoint (nineEdge 24) (nineEdge j)) :
    {nineEdge 24,nineEdge j,Finset.univ \ (nineEdge 24 ∪ nineEdge j)} =
      ninePartition (nineCompletion 24 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 24) (nineEdge j) →
    {nineEdge 24,nineEdge j,Finset.univ \ (nineEdge 24 ∪ nineEdge j)} =
      ninePartition (nineCompletion 24 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 24) (nineEdge j) →
    {nineEdge 24,nineEdge j,Finset.univ \ (nineEdge 24 ∪ nineEdge j)} =
      ninePartition (nineCompletion 24 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_25 (j : Fin 84) (h : Disjoint (nineEdge 25) (nineEdge j)) :
    {nineEdge 25,nineEdge j,Finset.univ \ (nineEdge 25 ∪ nineEdge j)} =
      ninePartition (nineCompletion 25 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 25) (nineEdge j) →
    {nineEdge 25,nineEdge j,Finset.univ \ (nineEdge 25 ∪ nineEdge j)} =
      ninePartition (nineCompletion 25 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 25) (nineEdge j) →
    {nineEdge 25,nineEdge j,Finset.univ \ (nineEdge 25 ∪ nineEdge j)} =
      ninePartition (nineCompletion 25 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_26 (j : Fin 84) (h : Disjoint (nineEdge 26) (nineEdge j)) :
    {nineEdge 26,nineEdge j,Finset.univ \ (nineEdge 26 ∪ nineEdge j)} =
      ninePartition (nineCompletion 26 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 26) (nineEdge j) →
    {nineEdge 26,nineEdge j,Finset.univ \ (nineEdge 26 ∪ nineEdge j)} =
      ninePartition (nineCompletion 26 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 26) (nineEdge j) →
    {nineEdge 26,nineEdge j,Finset.univ \ (nineEdge 26 ∪ nineEdge j)} =
      ninePartition (nineCompletion 26 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_27 (j : Fin 84) (h : Disjoint (nineEdge 27) (nineEdge j)) :
    {nineEdge 27,nineEdge j,Finset.univ \ (nineEdge 27 ∪ nineEdge j)} =
      ninePartition (nineCompletion 27 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 27) (nineEdge j) →
    {nineEdge 27,nineEdge j,Finset.univ \ (nineEdge 27 ∪ nineEdge j)} =
      ninePartition (nineCompletion 27 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 27) (nineEdge j) →
    {nineEdge 27,nineEdge j,Finset.univ \ (nineEdge 27 ∪ nineEdge j)} =
      ninePartition (nineCompletion 27 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_28 (j : Fin 84) (h : Disjoint (nineEdge 28) (nineEdge j)) :
    {nineEdge 28,nineEdge j,Finset.univ \ (nineEdge 28 ∪ nineEdge j)} =
      ninePartition (nineCompletion 28 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 28) (nineEdge j) →
    {nineEdge 28,nineEdge j,Finset.univ \ (nineEdge 28 ∪ nineEdge j)} =
      ninePartition (nineCompletion 28 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 28) (nineEdge j) →
    {nineEdge 28,nineEdge j,Finset.univ \ (nineEdge 28 ∪ nineEdge j)} =
      ninePartition (nineCompletion 28 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_29 (j : Fin 84) (h : Disjoint (nineEdge 29) (nineEdge j)) :
    {nineEdge 29,nineEdge j,Finset.univ \ (nineEdge 29 ∪ nineEdge j)} =
      ninePartition (nineCompletion 29 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 29) (nineEdge j) →
    {nineEdge 29,nineEdge j,Finset.univ \ (nineEdge 29 ∪ nineEdge j)} =
      ninePartition (nineCompletion 29 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 29) (nineEdge j) →
    {nineEdge 29,nineEdge j,Finset.univ \ (nineEdge 29 ∪ nineEdge j)} =
      ninePartition (nineCompletion 29 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_30 (j : Fin 84) (h : Disjoint (nineEdge 30) (nineEdge j)) :
    {nineEdge 30,nineEdge j,Finset.univ \ (nineEdge 30 ∪ nineEdge j)} =
      ninePartition (nineCompletion 30 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 30) (nineEdge j) →
    {nineEdge 30,nineEdge j,Finset.univ \ (nineEdge 30 ∪ nineEdge j)} =
      ninePartition (nineCompletion 30 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 30) (nineEdge j) →
    {nineEdge 30,nineEdge j,Finset.univ \ (nineEdge 30 ∪ nineEdge j)} =
      ninePartition (nineCompletion 30 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_31 (j : Fin 84) (h : Disjoint (nineEdge 31) (nineEdge j)) :
    {nineEdge 31,nineEdge j,Finset.univ \ (nineEdge 31 ∪ nineEdge j)} =
      ninePartition (nineCompletion 31 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 31) (nineEdge j) →
    {nineEdge 31,nineEdge j,Finset.univ \ (nineEdge 31 ∪ nineEdge j)} =
      ninePartition (nineCompletion 31 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 31) (nineEdge j) →
    {nineEdge 31,nineEdge j,Finset.univ \ (nineEdge 31 ∪ nineEdge j)} =
      ninePartition (nineCompletion 31 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_32 (j : Fin 84) (h : Disjoint (nineEdge 32) (nineEdge j)) :
    {nineEdge 32,nineEdge j,Finset.univ \ (nineEdge 32 ∪ nineEdge j)} =
      ninePartition (nineCompletion 32 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 32) (nineEdge j) →
    {nineEdge 32,nineEdge j,Finset.univ \ (nineEdge 32 ∪ nineEdge j)} =
      ninePartition (nineCompletion 32 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 32) (nineEdge j) →
    {nineEdge 32,nineEdge j,Finset.univ \ (nineEdge 32 ∪ nineEdge j)} =
      ninePartition (nineCompletion 32 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_33 (j : Fin 84) (h : Disjoint (nineEdge 33) (nineEdge j)) :
    {nineEdge 33,nineEdge j,Finset.univ \ (nineEdge 33 ∪ nineEdge j)} =
      ninePartition (nineCompletion 33 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 33) (nineEdge j) →
    {nineEdge 33,nineEdge j,Finset.univ \ (nineEdge 33 ∪ nineEdge j)} =
      ninePartition (nineCompletion 33 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 33) (nineEdge j) →
    {nineEdge 33,nineEdge j,Finset.univ \ (nineEdge 33 ∪ nineEdge j)} =
      ninePartition (nineCompletion 33 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_34 (j : Fin 84) (h : Disjoint (nineEdge 34) (nineEdge j)) :
    {nineEdge 34,nineEdge j,Finset.univ \ (nineEdge 34 ∪ nineEdge j)} =
      ninePartition (nineCompletion 34 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 34) (nineEdge j) →
    {nineEdge 34,nineEdge j,Finset.univ \ (nineEdge 34 ∪ nineEdge j)} =
      ninePartition (nineCompletion 34 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 34) (nineEdge j) →
    {nineEdge 34,nineEdge j,Finset.univ \ (nineEdge 34 ∪ nineEdge j)} =
      ninePartition (nineCompletion 34 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_35 (j : Fin 84) (h : Disjoint (nineEdge 35) (nineEdge j)) :
    {nineEdge 35,nineEdge j,Finset.univ \ (nineEdge 35 ∪ nineEdge j)} =
      ninePartition (nineCompletion 35 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 35) (nineEdge j) →
    {nineEdge 35,nineEdge j,Finset.univ \ (nineEdge 35 ∪ nineEdge j)} =
      ninePartition (nineCompletion 35 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 35) (nineEdge j) →
    {nineEdge 35,nineEdge j,Finset.univ \ (nineEdge 35 ∪ nineEdge j)} =
      ninePartition (nineCompletion 35 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_36 (j : Fin 84) (h : Disjoint (nineEdge 36) (nineEdge j)) :
    {nineEdge 36,nineEdge j,Finset.univ \ (nineEdge 36 ∪ nineEdge j)} =
      ninePartition (nineCompletion 36 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 36) (nineEdge j) →
    {nineEdge 36,nineEdge j,Finset.univ \ (nineEdge 36 ∪ nineEdge j)} =
      ninePartition (nineCompletion 36 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 36) (nineEdge j) →
    {nineEdge 36,nineEdge j,Finset.univ \ (nineEdge 36 ∪ nineEdge j)} =
      ninePartition (nineCompletion 36 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_37 (j : Fin 84) (h : Disjoint (nineEdge 37) (nineEdge j)) :
    {nineEdge 37,nineEdge j,Finset.univ \ (nineEdge 37 ∪ nineEdge j)} =
      ninePartition (nineCompletion 37 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 37) (nineEdge j) →
    {nineEdge 37,nineEdge j,Finset.univ \ (nineEdge 37 ∪ nineEdge j)} =
      ninePartition (nineCompletion 37 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 37) (nineEdge j) →
    {nineEdge 37,nineEdge j,Finset.univ \ (nineEdge 37 ∪ nineEdge j)} =
      ninePartition (nineCompletion 37 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_38 (j : Fin 84) (h : Disjoint (nineEdge 38) (nineEdge j)) :
    {nineEdge 38,nineEdge j,Finset.univ \ (nineEdge 38 ∪ nineEdge j)} =
      ninePartition (nineCompletion 38 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 38) (nineEdge j) →
    {nineEdge 38,nineEdge j,Finset.univ \ (nineEdge 38 ∪ nineEdge j)} =
      ninePartition (nineCompletion 38 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 38) (nineEdge j) →
    {nineEdge 38,nineEdge j,Finset.univ \ (nineEdge 38 ∪ nineEdge j)} =
      ninePartition (nineCompletion 38 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_39 (j : Fin 84) (h : Disjoint (nineEdge 39) (nineEdge j)) :
    {nineEdge 39,nineEdge j,Finset.univ \ (nineEdge 39 ∪ nineEdge j)} =
      ninePartition (nineCompletion 39 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 39) (nineEdge j) →
    {nineEdge 39,nineEdge j,Finset.univ \ (nineEdge 39 ∪ nineEdge j)} =
      ninePartition (nineCompletion 39 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 39) (nineEdge j) →
    {nineEdge 39,nineEdge j,Finset.univ \ (nineEdge 39 ∪ nineEdge j)} =
      ninePartition (nineCompletion 39 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_40 (j : Fin 84) (h : Disjoint (nineEdge 40) (nineEdge j)) :
    {nineEdge 40,nineEdge j,Finset.univ \ (nineEdge 40 ∪ nineEdge j)} =
      ninePartition (nineCompletion 40 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 40) (nineEdge j) →
    {nineEdge 40,nineEdge j,Finset.univ \ (nineEdge 40 ∪ nineEdge j)} =
      ninePartition (nineCompletion 40 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 40) (nineEdge j) →
    {nineEdge 40,nineEdge j,Finset.univ \ (nineEdge 40 ∪ nineEdge j)} =
      ninePartition (nineCompletion 40 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_41 (j : Fin 84) (h : Disjoint (nineEdge 41) (nineEdge j)) :
    {nineEdge 41,nineEdge j,Finset.univ \ (nineEdge 41 ∪ nineEdge j)} =
      ninePartition (nineCompletion 41 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 41) (nineEdge j) →
    {nineEdge 41,nineEdge j,Finset.univ \ (nineEdge 41 ∪ nineEdge j)} =
      ninePartition (nineCompletion 41 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 41) (nineEdge j) →
    {nineEdge 41,nineEdge j,Finset.univ \ (nineEdge 41 ∪ nineEdge j)} =
      ninePartition (nineCompletion 41 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_42 (j : Fin 84) (h : Disjoint (nineEdge 42) (nineEdge j)) :
    {nineEdge 42,nineEdge j,Finset.univ \ (nineEdge 42 ∪ nineEdge j)} =
      ninePartition (nineCompletion 42 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 42) (nineEdge j) →
    {nineEdge 42,nineEdge j,Finset.univ \ (nineEdge 42 ∪ nineEdge j)} =
      ninePartition (nineCompletion 42 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 42) (nineEdge j) →
    {nineEdge 42,nineEdge j,Finset.univ \ (nineEdge 42 ∪ nineEdge j)} =
      ninePartition (nineCompletion 42 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_43 (j : Fin 84) (h : Disjoint (nineEdge 43) (nineEdge j)) :
    {nineEdge 43,nineEdge j,Finset.univ \ (nineEdge 43 ∪ nineEdge j)} =
      ninePartition (nineCompletion 43 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 43) (nineEdge j) →
    {nineEdge 43,nineEdge j,Finset.univ \ (nineEdge 43 ∪ nineEdge j)} =
      ninePartition (nineCompletion 43 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 43) (nineEdge j) →
    {nineEdge 43,nineEdge j,Finset.univ \ (nineEdge 43 ∪ nineEdge j)} =
      ninePartition (nineCompletion 43 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_44 (j : Fin 84) (h : Disjoint (nineEdge 44) (nineEdge j)) :
    {nineEdge 44,nineEdge j,Finset.univ \ (nineEdge 44 ∪ nineEdge j)} =
      ninePartition (nineCompletion 44 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 44) (nineEdge j) →
    {nineEdge 44,nineEdge j,Finset.univ \ (nineEdge 44 ∪ nineEdge j)} =
      ninePartition (nineCompletion 44 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 44) (nineEdge j) →
    {nineEdge 44,nineEdge j,Finset.univ \ (nineEdge 44 ∪ nineEdge j)} =
      ninePartition (nineCompletion 44 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_45 (j : Fin 84) (h : Disjoint (nineEdge 45) (nineEdge j)) :
    {nineEdge 45,nineEdge j,Finset.univ \ (nineEdge 45 ∪ nineEdge j)} =
      ninePartition (nineCompletion 45 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 45) (nineEdge j) →
    {nineEdge 45,nineEdge j,Finset.univ \ (nineEdge 45 ∪ nineEdge j)} =
      ninePartition (nineCompletion 45 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 45) (nineEdge j) →
    {nineEdge 45,nineEdge j,Finset.univ \ (nineEdge 45 ∪ nineEdge j)} =
      ninePartition (nineCompletion 45 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_46 (j : Fin 84) (h : Disjoint (nineEdge 46) (nineEdge j)) :
    {nineEdge 46,nineEdge j,Finset.univ \ (nineEdge 46 ∪ nineEdge j)} =
      ninePartition (nineCompletion 46 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 46) (nineEdge j) →
    {nineEdge 46,nineEdge j,Finset.univ \ (nineEdge 46 ∪ nineEdge j)} =
      ninePartition (nineCompletion 46 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 46) (nineEdge j) →
    {nineEdge 46,nineEdge j,Finset.univ \ (nineEdge 46 ∪ nineEdge j)} =
      ninePartition (nineCompletion 46 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_47 (j : Fin 84) (h : Disjoint (nineEdge 47) (nineEdge j)) :
    {nineEdge 47,nineEdge j,Finset.univ \ (nineEdge 47 ∪ nineEdge j)} =
      ninePartition (nineCompletion 47 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 47) (nineEdge j) →
    {nineEdge 47,nineEdge j,Finset.univ \ (nineEdge 47 ∪ nineEdge j)} =
      ninePartition (nineCompletion 47 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 47) (nineEdge j) →
    {nineEdge 47,nineEdge j,Finset.univ \ (nineEdge 47 ∪ nineEdge j)} =
      ninePartition (nineCompletion 47 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_48 (j : Fin 84) (h : Disjoint (nineEdge 48) (nineEdge j)) :
    {nineEdge 48,nineEdge j,Finset.univ \ (nineEdge 48 ∪ nineEdge j)} =
      ninePartition (nineCompletion 48 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 48) (nineEdge j) →
    {nineEdge 48,nineEdge j,Finset.univ \ (nineEdge 48 ∪ nineEdge j)} =
      ninePartition (nineCompletion 48 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 48) (nineEdge j) →
    {nineEdge 48,nineEdge j,Finset.univ \ (nineEdge 48 ∪ nineEdge j)} =
      ninePartition (nineCompletion 48 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_49 (j : Fin 84) (h : Disjoint (nineEdge 49) (nineEdge j)) :
    {nineEdge 49,nineEdge j,Finset.univ \ (nineEdge 49 ∪ nineEdge j)} =
      ninePartition (nineCompletion 49 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 49) (nineEdge j) →
    {nineEdge 49,nineEdge j,Finset.univ \ (nineEdge 49 ∪ nineEdge j)} =
      ninePartition (nineCompletion 49 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 49) (nineEdge j) →
    {nineEdge 49,nineEdge j,Finset.univ \ (nineEdge 49 ∪ nineEdge j)} =
      ninePartition (nineCompletion 49 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_50 (j : Fin 84) (h : Disjoint (nineEdge 50) (nineEdge j)) :
    {nineEdge 50,nineEdge j,Finset.univ \ (nineEdge 50 ∪ nineEdge j)} =
      ninePartition (nineCompletion 50 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 50) (nineEdge j) →
    {nineEdge 50,nineEdge j,Finset.univ \ (nineEdge 50 ∪ nineEdge j)} =
      ninePartition (nineCompletion 50 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 50) (nineEdge j) →
    {nineEdge 50,nineEdge j,Finset.univ \ (nineEdge 50 ∪ nineEdge j)} =
      ninePartition (nineCompletion 50 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_51 (j : Fin 84) (h : Disjoint (nineEdge 51) (nineEdge j)) :
    {nineEdge 51,nineEdge j,Finset.univ \ (nineEdge 51 ∪ nineEdge j)} =
      ninePartition (nineCompletion 51 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 51) (nineEdge j) →
    {nineEdge 51,nineEdge j,Finset.univ \ (nineEdge 51 ∪ nineEdge j)} =
      ninePartition (nineCompletion 51 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 51) (nineEdge j) →
    {nineEdge 51,nineEdge j,Finset.univ \ (nineEdge 51 ∪ nineEdge j)} =
      ninePartition (nineCompletion 51 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_52 (j : Fin 84) (h : Disjoint (nineEdge 52) (nineEdge j)) :
    {nineEdge 52,nineEdge j,Finset.univ \ (nineEdge 52 ∪ nineEdge j)} =
      ninePartition (nineCompletion 52 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 52) (nineEdge j) →
    {nineEdge 52,nineEdge j,Finset.univ \ (nineEdge 52 ∪ nineEdge j)} =
      ninePartition (nineCompletion 52 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 52) (nineEdge j) →
    {nineEdge 52,nineEdge j,Finset.univ \ (nineEdge 52 ∪ nineEdge j)} =
      ninePartition (nineCompletion 52 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_53 (j : Fin 84) (h : Disjoint (nineEdge 53) (nineEdge j)) :
    {nineEdge 53,nineEdge j,Finset.univ \ (nineEdge 53 ∪ nineEdge j)} =
      ninePartition (nineCompletion 53 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 53) (nineEdge j) →
    {nineEdge 53,nineEdge j,Finset.univ \ (nineEdge 53 ∪ nineEdge j)} =
      ninePartition (nineCompletion 53 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 53) (nineEdge j) →
    {nineEdge 53,nineEdge j,Finset.univ \ (nineEdge 53 ∪ nineEdge j)} =
      ninePartition (nineCompletion 53 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_54 (j : Fin 84) (h : Disjoint (nineEdge 54) (nineEdge j)) :
    {nineEdge 54,nineEdge j,Finset.univ \ (nineEdge 54 ∪ nineEdge j)} =
      ninePartition (nineCompletion 54 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 54) (nineEdge j) →
    {nineEdge 54,nineEdge j,Finset.univ \ (nineEdge 54 ∪ nineEdge j)} =
      ninePartition (nineCompletion 54 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 54) (nineEdge j) →
    {nineEdge 54,nineEdge j,Finset.univ \ (nineEdge 54 ∪ nineEdge j)} =
      ninePartition (nineCompletion 54 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_55 (j : Fin 84) (h : Disjoint (nineEdge 55) (nineEdge j)) :
    {nineEdge 55,nineEdge j,Finset.univ \ (nineEdge 55 ∪ nineEdge j)} =
      ninePartition (nineCompletion 55 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 55) (nineEdge j) →
    {nineEdge 55,nineEdge j,Finset.univ \ (nineEdge 55 ∪ nineEdge j)} =
      ninePartition (nineCompletion 55 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 55) (nineEdge j) →
    {nineEdge 55,nineEdge j,Finset.univ \ (nineEdge 55 ∪ nineEdge j)} =
      ninePartition (nineCompletion 55 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_56 (j : Fin 84) (h : Disjoint (nineEdge 56) (nineEdge j)) :
    {nineEdge 56,nineEdge j,Finset.univ \ (nineEdge 56 ∪ nineEdge j)} =
      ninePartition (nineCompletion 56 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 56) (nineEdge j) →
    {nineEdge 56,nineEdge j,Finset.univ \ (nineEdge 56 ∪ nineEdge j)} =
      ninePartition (nineCompletion 56 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 56) (nineEdge j) →
    {nineEdge 56,nineEdge j,Finset.univ \ (nineEdge 56 ∪ nineEdge j)} =
      ninePartition (nineCompletion 56 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_57 (j : Fin 84) (h : Disjoint (nineEdge 57) (nineEdge j)) :
    {nineEdge 57,nineEdge j,Finset.univ \ (nineEdge 57 ∪ nineEdge j)} =
      ninePartition (nineCompletion 57 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 57) (nineEdge j) →
    {nineEdge 57,nineEdge j,Finset.univ \ (nineEdge 57 ∪ nineEdge j)} =
      ninePartition (nineCompletion 57 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 57) (nineEdge j) →
    {nineEdge 57,nineEdge j,Finset.univ \ (nineEdge 57 ∪ nineEdge j)} =
      ninePartition (nineCompletion 57 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_58 (j : Fin 84) (h : Disjoint (nineEdge 58) (nineEdge j)) :
    {nineEdge 58,nineEdge j,Finset.univ \ (nineEdge 58 ∪ nineEdge j)} =
      ninePartition (nineCompletion 58 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 58) (nineEdge j) →
    {nineEdge 58,nineEdge j,Finset.univ \ (nineEdge 58 ∪ nineEdge j)} =
      ninePartition (nineCompletion 58 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 58) (nineEdge j) →
    {nineEdge 58,nineEdge j,Finset.univ \ (nineEdge 58 ∪ nineEdge j)} =
      ninePartition (nineCompletion 58 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_59 (j : Fin 84) (h : Disjoint (nineEdge 59) (nineEdge j)) :
    {nineEdge 59,nineEdge j,Finset.univ \ (nineEdge 59 ∪ nineEdge j)} =
      ninePartition (nineCompletion 59 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 59) (nineEdge j) →
    {nineEdge 59,nineEdge j,Finset.univ \ (nineEdge 59 ∪ nineEdge j)} =
      ninePartition (nineCompletion 59 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 59) (nineEdge j) →
    {nineEdge 59,nineEdge j,Finset.univ \ (nineEdge 59 ∪ nineEdge j)} =
      ninePartition (nineCompletion 59 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_60 (j : Fin 84) (h : Disjoint (nineEdge 60) (nineEdge j)) :
    {nineEdge 60,nineEdge j,Finset.univ \ (nineEdge 60 ∪ nineEdge j)} =
      ninePartition (nineCompletion 60 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 60) (nineEdge j) →
    {nineEdge 60,nineEdge j,Finset.univ \ (nineEdge 60 ∪ nineEdge j)} =
      ninePartition (nineCompletion 60 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 60) (nineEdge j) →
    {nineEdge 60,nineEdge j,Finset.univ \ (nineEdge 60 ∪ nineEdge j)} =
      ninePartition (nineCompletion 60 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_61 (j : Fin 84) (h : Disjoint (nineEdge 61) (nineEdge j)) :
    {nineEdge 61,nineEdge j,Finset.univ \ (nineEdge 61 ∪ nineEdge j)} =
      ninePartition (nineCompletion 61 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 61) (nineEdge j) →
    {nineEdge 61,nineEdge j,Finset.univ \ (nineEdge 61 ∪ nineEdge j)} =
      ninePartition (nineCompletion 61 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 61) (nineEdge j) →
    {nineEdge 61,nineEdge j,Finset.univ \ (nineEdge 61 ∪ nineEdge j)} =
      ninePartition (nineCompletion 61 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_62 (j : Fin 84) (h : Disjoint (nineEdge 62) (nineEdge j)) :
    {nineEdge 62,nineEdge j,Finset.univ \ (nineEdge 62 ∪ nineEdge j)} =
      ninePartition (nineCompletion 62 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 62) (nineEdge j) →
    {nineEdge 62,nineEdge j,Finset.univ \ (nineEdge 62 ∪ nineEdge j)} =
      ninePartition (nineCompletion 62 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 62) (nineEdge j) →
    {nineEdge 62,nineEdge j,Finset.univ \ (nineEdge 62 ∪ nineEdge j)} =
      ninePartition (nineCompletion 62 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_63 (j : Fin 84) (h : Disjoint (nineEdge 63) (nineEdge j)) :
    {nineEdge 63,nineEdge j,Finset.univ \ (nineEdge 63 ∪ nineEdge j)} =
      ninePartition (nineCompletion 63 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 63) (nineEdge j) →
    {nineEdge 63,nineEdge j,Finset.univ \ (nineEdge 63 ∪ nineEdge j)} =
      ninePartition (nineCompletion 63 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 63) (nineEdge j) →
    {nineEdge 63,nineEdge j,Finset.univ \ (nineEdge 63 ∪ nineEdge j)} =
      ninePartition (nineCompletion 63 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_64 (j : Fin 84) (h : Disjoint (nineEdge 64) (nineEdge j)) :
    {nineEdge 64,nineEdge j,Finset.univ \ (nineEdge 64 ∪ nineEdge j)} =
      ninePartition (nineCompletion 64 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 64) (nineEdge j) →
    {nineEdge 64,nineEdge j,Finset.univ \ (nineEdge 64 ∪ nineEdge j)} =
      ninePartition (nineCompletion 64 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 64) (nineEdge j) →
    {nineEdge 64,nineEdge j,Finset.univ \ (nineEdge 64 ∪ nineEdge j)} =
      ninePartition (nineCompletion 64 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_65 (j : Fin 84) (h : Disjoint (nineEdge 65) (nineEdge j)) :
    {nineEdge 65,nineEdge j,Finset.univ \ (nineEdge 65 ∪ nineEdge j)} =
      ninePartition (nineCompletion 65 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 65) (nineEdge j) →
    {nineEdge 65,nineEdge j,Finset.univ \ (nineEdge 65 ∪ nineEdge j)} =
      ninePartition (nineCompletion 65 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 65) (nineEdge j) →
    {nineEdge 65,nineEdge j,Finset.univ \ (nineEdge 65 ∪ nineEdge j)} =
      ninePartition (nineCompletion 65 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_66 (j : Fin 84) (h : Disjoint (nineEdge 66) (nineEdge j)) :
    {nineEdge 66,nineEdge j,Finset.univ \ (nineEdge 66 ∪ nineEdge j)} =
      ninePartition (nineCompletion 66 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 66) (nineEdge j) →
    {nineEdge 66,nineEdge j,Finset.univ \ (nineEdge 66 ∪ nineEdge j)} =
      ninePartition (nineCompletion 66 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 66) (nineEdge j) →
    {nineEdge 66,nineEdge j,Finset.univ \ (nineEdge 66 ∪ nineEdge j)} =
      ninePartition (nineCompletion 66 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_67 (j : Fin 84) (h : Disjoint (nineEdge 67) (nineEdge j)) :
    {nineEdge 67,nineEdge j,Finset.univ \ (nineEdge 67 ∪ nineEdge j)} =
      ninePartition (nineCompletion 67 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 67) (nineEdge j) →
    {nineEdge 67,nineEdge j,Finset.univ \ (nineEdge 67 ∪ nineEdge j)} =
      ninePartition (nineCompletion 67 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 67) (nineEdge j) →
    {nineEdge 67,nineEdge j,Finset.univ \ (nineEdge 67 ∪ nineEdge j)} =
      ninePartition (nineCompletion 67 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_68 (j : Fin 84) (h : Disjoint (nineEdge 68) (nineEdge j)) :
    {nineEdge 68,nineEdge j,Finset.univ \ (nineEdge 68 ∪ nineEdge j)} =
      ninePartition (nineCompletion 68 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 68) (nineEdge j) →
    {nineEdge 68,nineEdge j,Finset.univ \ (nineEdge 68 ∪ nineEdge j)} =
      ninePartition (nineCompletion 68 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 68) (nineEdge j) →
    {nineEdge 68,nineEdge j,Finset.univ \ (nineEdge 68 ∪ nineEdge j)} =
      ninePartition (nineCompletion 68 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_69 (j : Fin 84) (h : Disjoint (nineEdge 69) (nineEdge j)) :
    {nineEdge 69,nineEdge j,Finset.univ \ (nineEdge 69 ∪ nineEdge j)} =
      ninePartition (nineCompletion 69 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 69) (nineEdge j) →
    {nineEdge 69,nineEdge j,Finset.univ \ (nineEdge 69 ∪ nineEdge j)} =
      ninePartition (nineCompletion 69 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 69) (nineEdge j) →
    {nineEdge 69,nineEdge j,Finset.univ \ (nineEdge 69 ∪ nineEdge j)} =
      ninePartition (nineCompletion 69 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_70 (j : Fin 84) (h : Disjoint (nineEdge 70) (nineEdge j)) :
    {nineEdge 70,nineEdge j,Finset.univ \ (nineEdge 70 ∪ nineEdge j)} =
      ninePartition (nineCompletion 70 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 70) (nineEdge j) →
    {nineEdge 70,nineEdge j,Finset.univ \ (nineEdge 70 ∪ nineEdge j)} =
      ninePartition (nineCompletion 70 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 70) (nineEdge j) →
    {nineEdge 70,nineEdge j,Finset.univ \ (nineEdge 70 ∪ nineEdge j)} =
      ninePartition (nineCompletion 70 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_71 (j : Fin 84) (h : Disjoint (nineEdge 71) (nineEdge j)) :
    {nineEdge 71,nineEdge j,Finset.univ \ (nineEdge 71 ∪ nineEdge j)} =
      ninePartition (nineCompletion 71 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 71) (nineEdge j) →
    {nineEdge 71,nineEdge j,Finset.univ \ (nineEdge 71 ∪ nineEdge j)} =
      ninePartition (nineCompletion 71 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 71) (nineEdge j) →
    {nineEdge 71,nineEdge j,Finset.univ \ (nineEdge 71 ∪ nineEdge j)} =
      ninePartition (nineCompletion 71 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_72 (j : Fin 84) (h : Disjoint (nineEdge 72) (nineEdge j)) :
    {nineEdge 72,nineEdge j,Finset.univ \ (nineEdge 72 ∪ nineEdge j)} =
      ninePartition (nineCompletion 72 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 72) (nineEdge j) →
    {nineEdge 72,nineEdge j,Finset.univ \ (nineEdge 72 ∪ nineEdge j)} =
      ninePartition (nineCompletion 72 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 72) (nineEdge j) →
    {nineEdge 72,nineEdge j,Finset.univ \ (nineEdge 72 ∪ nineEdge j)} =
      ninePartition (nineCompletion 72 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_73 (j : Fin 84) (h : Disjoint (nineEdge 73) (nineEdge j)) :
    {nineEdge 73,nineEdge j,Finset.univ \ (nineEdge 73 ∪ nineEdge j)} =
      ninePartition (nineCompletion 73 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 73) (nineEdge j) →
    {nineEdge 73,nineEdge j,Finset.univ \ (nineEdge 73 ∪ nineEdge j)} =
      ninePartition (nineCompletion 73 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 73) (nineEdge j) →
    {nineEdge 73,nineEdge j,Finset.univ \ (nineEdge 73 ∪ nineEdge j)} =
      ninePartition (nineCompletion 73 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_74 (j : Fin 84) (h : Disjoint (nineEdge 74) (nineEdge j)) :
    {nineEdge 74,nineEdge j,Finset.univ \ (nineEdge 74 ∪ nineEdge j)} =
      ninePartition (nineCompletion 74 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 74) (nineEdge j) →
    {nineEdge 74,nineEdge j,Finset.univ \ (nineEdge 74 ∪ nineEdge j)} =
      ninePartition (nineCompletion 74 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 74) (nineEdge j) →
    {nineEdge 74,nineEdge j,Finset.univ \ (nineEdge 74 ∪ nineEdge j)} =
      ninePartition (nineCompletion 74 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_75 (j : Fin 84) (h : Disjoint (nineEdge 75) (nineEdge j)) :
    {nineEdge 75,nineEdge j,Finset.univ \ (nineEdge 75 ∪ nineEdge j)} =
      ninePartition (nineCompletion 75 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 75) (nineEdge j) →
    {nineEdge 75,nineEdge j,Finset.univ \ (nineEdge 75 ∪ nineEdge j)} =
      ninePartition (nineCompletion 75 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 75) (nineEdge j) →
    {nineEdge 75,nineEdge j,Finset.univ \ (nineEdge 75 ∪ nineEdge j)} =
      ninePartition (nineCompletion 75 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_76 (j : Fin 84) (h : Disjoint (nineEdge 76) (nineEdge j)) :
    {nineEdge 76,nineEdge j,Finset.univ \ (nineEdge 76 ∪ nineEdge j)} =
      ninePartition (nineCompletion 76 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 76) (nineEdge j) →
    {nineEdge 76,nineEdge j,Finset.univ \ (nineEdge 76 ∪ nineEdge j)} =
      ninePartition (nineCompletion 76 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 76) (nineEdge j) →
    {nineEdge 76,nineEdge j,Finset.univ \ (nineEdge 76 ∪ nineEdge j)} =
      ninePartition (nineCompletion 76 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_77 (j : Fin 84) (h : Disjoint (nineEdge 77) (nineEdge j)) :
    {nineEdge 77,nineEdge j,Finset.univ \ (nineEdge 77 ∪ nineEdge j)} =
      ninePartition (nineCompletion 77 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 77) (nineEdge j) →
    {nineEdge 77,nineEdge j,Finset.univ \ (nineEdge 77 ∪ nineEdge j)} =
      ninePartition (nineCompletion 77 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 77) (nineEdge j) →
    {nineEdge 77,nineEdge j,Finset.univ \ (nineEdge 77 ∪ nineEdge j)} =
      ninePartition (nineCompletion 77 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_78 (j : Fin 84) (h : Disjoint (nineEdge 78) (nineEdge j)) :
    {nineEdge 78,nineEdge j,Finset.univ \ (nineEdge 78 ∪ nineEdge j)} =
      ninePartition (nineCompletion 78 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 78) (nineEdge j) →
    {nineEdge 78,nineEdge j,Finset.univ \ (nineEdge 78 ∪ nineEdge j)} =
      ninePartition (nineCompletion 78 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 78) (nineEdge j) →
    {nineEdge 78,nineEdge j,Finset.univ \ (nineEdge 78 ∪ nineEdge j)} =
      ninePartition (nineCompletion 78 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_79 (j : Fin 84) (h : Disjoint (nineEdge 79) (nineEdge j)) :
    {nineEdge 79,nineEdge j,Finset.univ \ (nineEdge 79 ∪ nineEdge j)} =
      ninePartition (nineCompletion 79 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 79) (nineEdge j) →
    {nineEdge 79,nineEdge j,Finset.univ \ (nineEdge 79 ∪ nineEdge j)} =
      ninePartition (nineCompletion 79 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 79) (nineEdge j) →
    {nineEdge 79,nineEdge j,Finset.univ \ (nineEdge 79 ∪ nineEdge j)} =
      ninePartition (nineCompletion 79 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_80 (j : Fin 84) (h : Disjoint (nineEdge 80) (nineEdge j)) :
    {nineEdge 80,nineEdge j,Finset.univ \ (nineEdge 80 ∪ nineEdge j)} =
      ninePartition (nineCompletion 80 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 80) (nineEdge j) →
    {nineEdge 80,nineEdge j,Finset.univ \ (nineEdge 80 ∪ nineEdge j)} =
      ninePartition (nineCompletion 80 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 80) (nineEdge j) →
    {nineEdge 80,nineEdge j,Finset.univ \ (nineEdge 80 ∪ nineEdge j)} =
      ninePartition (nineCompletion 80 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_81 (j : Fin 84) (h : Disjoint (nineEdge 81) (nineEdge j)) :
    {nineEdge 81,nineEdge j,Finset.univ \ (nineEdge 81 ∪ nineEdge j)} =
      ninePartition (nineCompletion 81 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 81) (nineEdge j) →
    {nineEdge 81,nineEdge j,Finset.univ \ (nineEdge 81 ∪ nineEdge j)} =
      ninePartition (nineCompletion 81 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 81) (nineEdge j) →
    {nineEdge 81,nineEdge j,Finset.univ \ (nineEdge 81 ∪ nineEdge j)} =
      ninePartition (nineCompletion 81 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_82 (j : Fin 84) (h : Disjoint (nineEdge 82) (nineEdge j)) :
    {nineEdge 82,nineEdge j,Finset.univ \ (nineEdge 82 ∪ nineEdge j)} =
      ninePartition (nineCompletion 82 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 82) (nineEdge j) →
    {nineEdge 82,nineEdge j,Finset.univ \ (nineEdge 82 ∪ nineEdge j)} =
      ninePartition (nineCompletion 82 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 82) (nineEdge j) →
    {nineEdge 82,nineEdge j,Finset.univ \ (nineEdge 82 ∪ nineEdge j)} =
      ninePartition (nineCompletion 82 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct_83 (j : Fin 84) (h : Disjoint (nineEdge 83) (nineEdge j)) :
    {nineEdge 83,nineEdge j,Finset.univ \ (nineEdge 83 ∪ nineEdge j)} =
      ninePartition (nineCompletion 83 j) := by
  have hc : (List.finRange 84).all (fun j => decide (Disjoint (nineEdge 83) (nineEdge j) →
    {nineEdge 83,nineEdge j,Finset.univ \ (nineEdge 83 ∪ nineEdge j)} =
      ninePartition (nineCompletion 83 j))) = true := by decide +kernel
  have hall : ∀ j : Fin 84, Disjoint (nineEdge 83) (nineEdge j) →
    {nineEdge 83,nineEdge j,Finset.univ \ (nineEdge 83 ∪ nineEdge j)} =
      ninePartition (nineCompletion 83 j) := by
    simpa only [List.all_eq_true,List.mem_finRange,true_implies,decide_eq_true_eq] using hc
  exact hall j h

 theorem nineCompletion_correct (i j : Fin 84) (h : Disjoint (nineEdge i) (nineEdge j)) :
    {nineEdge i,nineEdge j,Finset.univ \ (nineEdge i ∪ nineEdge j)} =
      ninePartition (nineCompletion i j) := by
  fin_cases i
  · exact nineCompletion_correct_0 j h
  · exact nineCompletion_correct_1 j h
  · exact nineCompletion_correct_2 j h
  · exact nineCompletion_correct_3 j h
  · exact nineCompletion_correct_4 j h
  · exact nineCompletion_correct_5 j h
  · exact nineCompletion_correct_6 j h
  · exact nineCompletion_correct_7 j h
  · exact nineCompletion_correct_8 j h
  · exact nineCompletion_correct_9 j h
  · exact nineCompletion_correct_10 j h
  · exact nineCompletion_correct_11 j h
  · exact nineCompletion_correct_12 j h
  · exact nineCompletion_correct_13 j h
  · exact nineCompletion_correct_14 j h
  · exact nineCompletion_correct_15 j h
  · exact nineCompletion_correct_16 j h
  · exact nineCompletion_correct_17 j h
  · exact nineCompletion_correct_18 j h
  · exact nineCompletion_correct_19 j h
  · exact nineCompletion_correct_20 j h
  · exact nineCompletion_correct_21 j h
  · exact nineCompletion_correct_22 j h
  · exact nineCompletion_correct_23 j h
  · exact nineCompletion_correct_24 j h
  · exact nineCompletion_correct_25 j h
  · exact nineCompletion_correct_26 j h
  · exact nineCompletion_correct_27 j h
  · exact nineCompletion_correct_28 j h
  · exact nineCompletion_correct_29 j h
  · exact nineCompletion_correct_30 j h
  · exact nineCompletion_correct_31 j h
  · exact nineCompletion_correct_32 j h
  · exact nineCompletion_correct_33 j h
  · exact nineCompletion_correct_34 j h
  · exact nineCompletion_correct_35 j h
  · exact nineCompletion_correct_36 j h
  · exact nineCompletion_correct_37 j h
  · exact nineCompletion_correct_38 j h
  · exact nineCompletion_correct_39 j h
  · exact nineCompletion_correct_40 j h
  · exact nineCompletion_correct_41 j h
  · exact nineCompletion_correct_42 j h
  · exact nineCompletion_correct_43 j h
  · exact nineCompletion_correct_44 j h
  · exact nineCompletion_correct_45 j h
  · exact nineCompletion_correct_46 j h
  · exact nineCompletion_correct_47 j h
  · exact nineCompletion_correct_48 j h
  · exact nineCompletion_correct_49 j h
  · exact nineCompletion_correct_50 j h
  · exact nineCompletion_correct_51 j h
  · exact nineCompletion_correct_52 j h
  · exact nineCompletion_correct_53 j h
  · exact nineCompletion_correct_54 j h
  · exact nineCompletion_correct_55 j h
  · exact nineCompletion_correct_56 j h
  · exact nineCompletion_correct_57 j h
  · exact nineCompletion_correct_58 j h
  · exact nineCompletion_correct_59 j h
  · exact nineCompletion_correct_60 j h
  · exact nineCompletion_correct_61 j h
  · exact nineCompletion_correct_62 j h
  · exact nineCompletion_correct_63 j h
  · exact nineCompletion_correct_64 j h
  · exact nineCompletion_correct_65 j h
  · exact nineCompletion_correct_66 j h
  · exact nineCompletion_correct_67 j h
  · exact nineCompletion_correct_68 j h
  · exact nineCompletion_correct_69 j h
  · exact nineCompletion_correct_70 j h
  · exact nineCompletion_correct_71 j h
  · exact nineCompletion_correct_72 j h
  · exact nineCompletion_correct_73 j h
  · exact nineCompletion_correct_74 j h
  · exact nineCompletion_correct_75 j h
  · exact nineCompletion_correct_76 j h
  · exact nineCompletion_correct_77 j h
  · exact nineCompletion_correct_78 j h
  · exact nineCompletion_correct_79 j h
  · exact nineCompletion_correct_80 j h
  · exact nineCompletion_correct_81 j h
  · exact nineCompletion_correct_82 j h
  · exact nineCompletion_correct_83 j h


/-- The finite table exhausts all ordinary perfect matchings of a 3-uniform
hypergraph on nine vertices. -/
theorem ninePartition_complete {H M : Hypergraph (Fin 9)}
    (hH : Uniform H 3) (hM : PerfectMatching H M) :
    ∃ i : Fin 280, M = ninePartition i := by
  have hc : M.card = 3 := by
    have hh := hM.card_mul_eq hH
    simp only [Fintype.card_fin] at hh
    omega
  obtain ⟨e,f,g,hef,heg,hfg,rfl⟩ := Finset.card_eq_three.mp hc
  have heH : e ∈ H := hM.subset (by simp)
  have hfH : f ∈ H := hM.subset (by simp)
  obtain ⟨i,rfl⟩ := nineEdge_complete e (hH e heH)
  obtain ⟨j,rfl⟩ := nineEdge_complete f (hH f hfH)
  have hdis : Disjoint (nineEdge i) (nineEdge j) :=
    hM.disjoint_edges (by simp) (by simp) hef
  have hg := third_edge_eq_complement hM heg hfg
  rw [hg]
  exact ⟨nineCompletion i j, nineCompletion_correct i j hdis⟩

end RigidGHZ.Finite
