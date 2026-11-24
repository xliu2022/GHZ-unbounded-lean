module

public import RigidGHZ.Finite.NineUpper
public import RigidGHZ.Finite.SixVertex
public import RigidGHZ.Finite.TripartiteClassification

/-! Fail the build if a principal finite theorem uses an axiom beyond the three
standard axioms allowed for the surrounding Mathlib development. Imported LRAT
declarations are traversed by Lean's ordinary dependency collector. -/

public meta section
open Lean Elab Command

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[
    `RigidGHZ.Finite.thirteen_rigid,
    `RigidGHZ.Finite.six_vertex_exact,
    `RigidGHZ.Finite.nine_vertex_exact,
    `RigidGHZ.Finite.balanced_tripartite_three_unique]
  for target in targets do
    let dependencies ← Lean.collectAxioms target
    for axiomName in dependencies do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom {axiomName} in {target}"
    let names := String.intercalate ", " (dependencies.toList.map Name.toString)
    logInfo m!"{target}: [{names}]"
