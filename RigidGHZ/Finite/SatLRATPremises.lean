module

public import RigidGHZ.Finite.SatLRATChunk

/-! Share the projections of a large CNF context. Every tree edge is checked
once, avoiding repeated reconstruction of the full root-to-leaf projection. -/

public meta section
namespace RigidGHZ.Finite
open Lean Elab Command Meta Term

partial def lratNamePremises (name : Name) (arr : Array (Array Int))
    (start stop : Nat) (formula parentProof : Expr) : MetaM Unit := do
  let ctx := Lean.mkConst (name ++ `context)
  let helperName := Name.num (Name.num (name ++ `subsumes) start) stop
  unless (← getEnv).contains helperName do
    addDecl <| Declaration.thmDecl {
      name := helperName, levelParams := [],
      type := mkApp2 (Lean.mkConst ``Sat.Fmla.subsumes) ctx formula,
      value := parentProof }
    resetCache
  let proof := Lean.mkConst helperName
  if stop - start == 1 then
    let clause := formula.appArg!
    let clauseName := lratClauseName name (start + 1)
    unless (← getEnv).contains clauseName do
      addDecl <| Declaration.thmDecl {
        name := clauseName, levelParams := [],
        type := mkApp2 (Lean.mkConst ``Sat.Fmla.proof) ctx clause,
        value := mkApp3 (Lean.mkConst ``Sat.Fmla.proof_of_subsumes) ctx clause proof }
      resetCache
  else
    let middle := start + (stop - start) / 2
    let left := formula.appFn!.appArg!
    let right := formula.appArg!
    lratNamePremises name arr start middle left
      (mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_left) ctx left right proof)
    lratNamePremises name arr middle stop right
      (mkApp4 (Lean.mkConst ``Sat.Fmla.subsumes_right) ctx left right proof)

elab "kernel_lrat_premises " n:ident cnf:term:max : command => do
  liftTermElabM do
    let name := (← getCurrNamespace) ++ n.getId
    let input ← unsafe evalTerm String (Lean.mkConst ``String) cnf
    let arr ← lratReadCNF input
    let ctx := Lean.mkConst (name ++ `context)
    let formula := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
    lratNamePremises name arr 0 arr.size formula
      (mkApp (Lean.mkConst ``Sat.Fmla.subsumes_self) ctx)

end RigidGHZ.Finite
