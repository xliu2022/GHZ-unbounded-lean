module

public import RigidGHZ.Finite.SatLRATChunk

/-! Reconstruct a self-contained chunk by reading the already checked types of
its premises. This avoids reparsing a large trace prefix for every module.
The same ordinary RUP proof builder and declaration checker are used. -/

public meta section
namespace RigidGHZ.Finite
open Lean Elab Command Meta Term

partial def lratLiteralArray (clause : Expr) : MetaM (Array Int) := do
  if clause.isConstOf ``Sat.Clause.nil then return #[]
  unless clause.isAppOfArity ``Sat.Clause.cons 2 do
    throwError "LRAT premise clause is not an explicit literal list"
  let args := clause.getAppArgs
  let literal := args[0]!
  let some variableIndex ← Meta.evalNat literal.appArg!
    | throwError "LRAT premise variable is not a numeral"
  let value : Int := if literal.isAppOfArity ``Sat.Literal.pos 1 then Int.ofNat variableIndex+1
    else if literal.isAppOfArity ``Sat.Literal.neg 1 then -(Int.ofNat variableIndex+1)
    else 0
  if value == 0 then throwError "unexpected LRAT premise literal"
  return #[value] ++ (← lratLiteralArray args[1]!)

def checkLRATDirect (name : Name) (trace : String) : MetaM Unit := do
  let ctx := Lean.mkConst (name ++ `context)
  let .success _ steps := Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_,trace.startPos⟩
    | throwError "invalid LRAT chunk"
  let mut db : Std.HashMap Nat Mathlib.Tactic.Sat.Clause := {}
  for step in steps do
    match step with
    | .del ids => db := ids.foldl (·.erase ·) db
    | .add id literals hints =>
      for ref in hints do
        let index := ref.natAbs
        unless db.contains index do
          let premiseName := lratClauseName name index
          let info ← getConstInfo premiseName
          unless info.type.isAppOfArity ``Sat.Fmla.proof 2 do
            throwError "unexpected type for imported LRAT premise {premiseName}"
          let clause := info.type.getAppArgs[1]!
          let lits ← lratLiteralArray clause
          db := db.insert index {lits,expr := clause,proof := Lean.mkConst premiseName}
      let clause := Mathlib.Tactic.Sat.buildClause literals
      let .ok proof := Mathlib.Tactic.Sat.buildProofStep db literals hints ctx clause
        | throwError "invalid direct LRAT inference {id}"
      let declName := lratClauseName name id
      addDecl <| Declaration.thmDecl {
        name := declName,levelParams := [],
        type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause,value := proof }
      resetCache
      db := db.insert id {lits := literals,expr := clause,proof := Lean.mkConst declName}
      if literals.isEmpty then
        addDecl <| Declaration.thmDecl {
          name,levelParams := [],type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause,
          value := Lean.mkConst declName }

elab "kernel_lrat_direct " n:ident trace:term:max : command => do
  liftTermElabM do
    let name := (← getCurrNamespace) ++ n.getId
    let input ← unsafe evalTerm String (Lean.mkConst ``String) trace
    checkLRATDirect name input

end RigidGHZ.Finite
