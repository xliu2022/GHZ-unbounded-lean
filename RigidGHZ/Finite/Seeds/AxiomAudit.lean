module

public import RigidGHZ.Finite.Seeds.UnrestrictedDegrees
public import RigidGHZ.Supplement.AffineSmallSeeds
public import RigidGHZ.Finite.Seeds.A11Seed
public import RigidGHZ.Finite.Seeds.A13Seed
public import RigidGHZ.Finite.Seeds.A17Seed
public import RigidGHZ.Finite.Seeds.A19Seed
public import RigidGHZ.Finite.Seeds.A23Seed
public import RigidGHZ.Finite.Seeds.A29Seed
public import RigidGHZ.Finite.Seeds.A31Seed
public import RigidGHZ.Finite.Seeds.A37Seed
public import RigidGHZ.Finite.Seeds.A41Seed
public import RigidGHZ.Finite.Seeds.A43Seed
public import RigidGHZ.Finite.Seeds.A47Seed

/-! Kernel dependency audit for every supplementary finite seed. -/
public meta section
open Lean Elab Command

run_cmd do
  let allowed := #[`propext, `Classical.choice, `Quot.sound]
  let targets := #[
    `RigidGHZ.Supplement.Affine.seed3,
    `RigidGHZ.Supplement.Affine.seed5,
    `RigidGHZ.Supplement.Affine.seed7,
    `RigidGHZ.Finite.Seeds.U12.rigid,
    `RigidGHZ.Finite.Seeds.U15.rigid,
    `RigidGHZ.Finite.Seeds.U18.rigid,
    `RigidGHZ.Finite.Seeds.U21.rigid,
    `RigidGHZ.Finite.Seeds.U24.rigid,
    `RigidGHZ.Finite.Seeds.U12.max_pair,
    `RigidGHZ.Finite.Seeds.U15.max_pair,
    `RigidGHZ.Finite.Seeds.U18.max_pair,
    `RigidGHZ.Finite.Seeds.U21.max_pair,
    `RigidGHZ.Finite.Seeds.U24.max_pair,
    `RigidGHZ.Finite.Seeds.A11.seed,
    `RigidGHZ.Finite.Seeds.A13.seed,
    `RigidGHZ.Finite.Seeds.A17.seed,
    `RigidGHZ.Finite.Seeds.A19.seed,
    `RigidGHZ.Finite.Seeds.A23.seed,
    `RigidGHZ.Finite.Seeds.A29.seed,
    `RigidGHZ.Finite.Seeds.A31.seed,
    `RigidGHZ.Finite.Seeds.A37.seed,
    `RigidGHZ.Finite.Seeds.A41.seed,
    `RigidGHZ.Finite.Seeds.A43.seed,
    `RigidGHZ.Finite.Seeds.A47.seed]
  for target in targets do
    let dependencies ← Lean.collectAxioms target
    for axiomName in dependencies do
      unless allowed.contains axiomName do
        throwError "Unapproved axiom {axiomName} in {target}"
    logInfo m!"{target}: [{String.intercalate ", " (dependencies.toList.map Name.toString)}]"
