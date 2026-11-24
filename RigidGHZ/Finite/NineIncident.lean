module

public import RigidGHZ.Finite.NineEnumeration

@[expose] public section
namespace RigidGHZ.Finite
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

/-- The 28 distinct triples incident with each vertex. -/
def nineIncidentTableRow0 : Array (Fin 84) := #[0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27]
def nineIncidentTableRow1 : Array (Fin 84) := #[0,1,2,3,4,5,6,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48]
def nineIncidentTableRow2 : Array (Fin 84) := #[0,7,8,9,10,11,12,28,29,30,31,32,33,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63]
def nineIncidentTableRow3 : Array (Fin 84) := #[1,7,13,14,15,16,17,28,34,35,36,37,38,49,50,51,52,53,64,65,66,67,68,69,70,71,72,73]
def nineIncidentTableRow4 : Array (Fin 84) := #[2,8,13,18,19,20,21,29,34,39,40,41,42,49,54,55,56,57,64,65,66,67,74,75,76,77,78,79]
def nineIncidentTableRow5 : Array (Fin 84) := #[3,9,14,18,22,23,24,30,35,39,43,44,45,50,54,58,59,60,64,68,69,70,74,75,76,80,81,82]
def nineIncidentTableRow6 : Array (Fin 84) := #[4,10,15,19,22,25,26,31,36,40,43,46,47,51,55,58,61,62,65,68,71,72,74,77,78,80,81,83]
def nineIncidentTableRow7 : Array (Fin 84) := #[5,11,16,20,23,25,27,32,37,41,44,46,48,52,56,59,61,63,66,69,71,73,75,77,79,80,82,83]
def nineIncidentTableRow8 : Array (Fin 84) := #[6,12,17,21,24,26,27,33,38,42,45,47,48,53,57,60,62,63,67,70,72,73,76,78,79,81,82,83]

def nineIncidentTable : Array (Array (Fin 84)) := #[nineIncidentTableRow0,nineIncidentTableRow1,nineIncidentTableRow2,nineIncidentTableRow3,nineIncidentTableRow4,nineIncidentTableRow5,nineIncidentTableRow6,nineIncidentTableRow7,nineIncidentTableRow8]

def nineIncident (v : Fin 9) (j : Fin 28) : Fin 84 := (nineIncidentTable[v.val]!)[j.val]!

 theorem nineIncident_injective (v : Fin 9) : Function.Injective (nineIncident v) := by
  have hc : (List.finRange 9).all (fun v => (List.finRange 28).all (fun i =>
    (List.finRange 28).all (fun j => decide (nineIncident v i = nineIncident v j → i = j)))) = true := by decide +kernel
  have h : ∀ v : Fin 9, Function.Injective (nineIncident v) := by
    simpa only [Function.Injective, List.all_eq_true, List.mem_finRange,
      true_implies, decide_eq_true_eq] using hc
  exact h v

 theorem nineIncident_complete (v : Fin 9) (e : Fin 84) :
    v ∈ nineEdge e ↔ ∃ j : Fin 28, nineIncident v j = e := by
  have hc : (List.finRange 9).all (fun v => (List.finRange 84).all (fun e =>
    decide (v ∈ nineEdge e ↔ ∃ j : Fin 28, nineIncident v j = e))) = true := by decide +kernel
  have h : ∀ v : Fin 9, ∀ e : Fin 84, v ∈ nineEdge e ↔ ∃ j : Fin 28, nineIncident v j = e := by
    simpa only [List.all_eq_true, List.mem_finRange, true_implies, decide_eq_true_eq] using hc
  exact h v e


end RigidGHZ.Finite
