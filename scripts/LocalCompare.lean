module

import Lake.Check.Compare
import Lake.Check.Axioms
import Lean.Data.Json.FromToJson.Basic
import Lean.Data.Json.Parser

/-!
Diagnostic comparison of locally generated exports using the unchanged
Comparator functions bundled with this Lean toolchain. This utility does not
provide process isolation and is not the Palomar full preflight. It never
imports the submitted Solution into the comparison process.
-/

open Lean

private def primitiveNames : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod,
  ``Nat.beq, ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft,
  ``Nat.shiftRight, ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce,
  ``Nat, ``String, ``String.mk, ``Char, ``optParam, ``autoParam,
  ``semiOutParam, ``outParam]

public def main (args : List String) : IO UInt32 := do
  let [configFile, challengeFile, solutionFile] := args
    | throw <| IO.userError "usage: LocalCompare.lean CONFIG CHALLENGE_EXPORT SOLUTION_EXPORT"
  let config ← IO.ofExcept <| Json.parse (← IO.FS.readFile configFile)
  let theorems ← IO.ofExcept <| config.getObjValAs? (Array String) "theorem_names"
  let axioms ← IO.ofExcept <| config.getObjValAs? (Array String) "permitted_axioms"
  let definitions := (config.getObjValAs? (Array String) "definition_names").toOption.getD #[]
  let theoremNames := theorems.map String.toName
  let axiomNames := axioms.map String.toName
  let definitionNames := definitions.map String.toName
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengeFile .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionFile .read)
  IO.ofExcept <| Lake.Check.compareAt challenge solution (theoremNames ++ axiomNames)
    definitionNames primitiveNames
  IO.println "PASS: exact declarations and transitive statement definitions match."
  IO.ofExcept <| Lake.Check.checkAxioms solution theoremNames definitionNames axiomNames
  IO.println "PASS: selected proof closures use only permitted axioms."
  for (axiomName, _) in Lake.Check.usedAxioms solution do
    IO.println s!"Exported axiom: {axiomName}"
  return 0
