module

public import RigidGHZ.Finite.SatKernel

/-! Large LRAT refutations are split across modules. Previously checked clauses
are imported as opaque theorems, bounding the memory required for one kernel
checking job. Every new clause is reconstructed by Mathlib's RUP proof builder. -/

public meta section
namespace RigidGHZ.Finite
open Lean Elab Command Meta Term

 def lratClauseName (name : Name) (id : ℕ) : Name := Name.num (name ++ `clause) id

 def lratReadCNF (s : String) : MetaM (Array (Array Int)) := do
  let .success _ (_,arr) := Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_,s.startPos⟩
    | throwError "invalid CNF input"
  if arr.isEmpty then throwError "empty CNF input"
  return arr

elab "kernel_lrat_context " n:ident cnf:term:max : command => do
  liftTermElabM do
    let name := (←getCurrNamespace) ++ n.getId
    let input ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let arr ← lratReadCNF input
    let value := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
    addDecl (Declaration.defnDecl {
      name := name ++ `context, levelParams := [], type := Lean.mkConst ``Sat.Fmla,
      value, hints := ReducibilityHints.regular 0, safety := .safe }) (forceExpose := true)

 def lratCheckChunk (name : Name) (cnf lrat : String) (start stop : ℕ) : MetaM Unit := do
  let arr ← lratReadCNF cnf
  let ctxName := name ++ `context
  let ctx := Lean.mkConst ctxName
  let ctx' := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
  let p := mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (Mathlib.Tactic.Sat.buildClauses arr ctx 0 arr.size ctx' p default).2
  let .success _ steps := Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_,lrat.startPos⟩
    | throwError "invalid LRAT input"
  let mut position := 0
  for step in steps do
    match step with
    | .del ids => db := ids.foldl (·.erase ·) db
    | .add id lits hints =>
      if position ≥ stop then return
      let clause := Mathlib.Tactic.Sat.buildClause lits
      let declName := lratClauseName name id
      if position < start then
        unless (←getEnv).contains declName do throwError "missing earlier LRAT clause {id}"
      else
        for ref in hints do
          let refId := ref.natAbs
          let some cl := db[refId]? | throwError "missing LRAT reference {refId}"
          let refName := lratClauseName name refId
          if (←getEnv).contains refName then
            db := db.insert refId {cl with proof := Lean.mkConst refName}
          else
            addDecl <| Declaration.thmDecl {
              name := refName, levelParams := [],
              type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx cl.expr, value := cl.proof }
            resetCache
            db := db.insert refId {cl with proof := Lean.mkConst refName}
        let .ok proof := Mathlib.Tactic.Sat.buildProofStep db lits hints ctx clause
          | throwError "invalid LRAT inference {id}"
        addDecl <| Declaration.thmDecl {
          name := declName, levelParams := [],
          type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause, value := proof }
        resetCache
      let proof := Lean.mkConst declName
      db := db.insert id {lits,expr := clause,proof}
      position := position + 1
      if lits.isEmpty then
        if position ≤ start then throwError "empty clause precedes current chunk"
        addDecl <| Declaration.thmDecl {
          name, levelParams := [], type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause,
          value := proof }
        return
  if position < stop then throwError "LRAT trace shorter than requested chunk"

elab "kernel_lrat_chunk " n:ident cnf:term:max lrat:term:max start:num stop:num : command => do
  liftTermElabM do
    let name := (←getCurrNamespace) ++ n.getId
    let cnf ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (Lean.mkConst ``String) lrat
    lratCheckChunk name cnf lrat start.getNat stop.getNat

end RigidGHZ.Finite
