module

public import RigidGHZ.Finite.ExactCoverAssemble

/-! Additional unit clauses for a counterexample normalized by a proved
automorphism. The units remain facts about actual edge membership. -/

@[expose] public section
namespace RigidGHZ.Finite

theorem exactCover_present {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) (M : Hypergraph V) (i : Fin e)
    (hi : D.edge i ∈ M) :
    Sat.Valuation.satisfies (D.valuation M) [Sat.Literal.pos i.val] := by
  intro hn
  exact hn ((D.valuation_edge M i).mpr hi)

theorem exactCover_absent {V : Type*} [DecidableEq V] {n e d : ℕ}
    (D : ExactCoverData V n e d) (M : Hypergraph V) (i : Fin e)
    (hi : D.edge i ∉ M) :
    Sat.Valuation.satisfies (D.valuation M) [Sat.Literal.neg i.val] := by
  intro h
  exact hi ((D.valuation_edge M i).mp h)

end RigidGHZ.Finite

public meta section
namespace RigidGHZ.Finite
open Lean Meta Elab Term Tactic Qq

def exactCoverNormalizedClause (entry : Json) (D C M hM hne hroot hlower : Expr) : MetaM Expr := do
  let .ok args := entry.getArr? | throwError "expected exact-cover metadata array"
  let .ok kind := args[0]!.getStr? | throwError "expected exact-cover clause kind"
  if kind != "present" && kind != "absent" then
    return ← exactCoverClauseProof entry D C M hM hne
  let params := (← inferType D).getAppArgs
  let some e ← Meta.evalNat params[params.size-2]!
    | throwError "exact-cover edge index size is not concrete"
  let .ok index := args[1]!.getNat? | throwError "expected unit-clause edge index"
  let i ← exactCoverFin e index
  if kind == "present" then
    return ← mkAppM ``exactCover_present #[D,M,i,hroot]
  let proof := mkApp hlower i
  let .forallE _ domain _ _ ← whnf (← inferType proof)
    | throwError "unexpected normalized exclusion hypothesis"
  let domain : Q(Prop) := domain
  let h ← mkDecideProofQ domain
  mkAppM ``exactCover_absent #[D,M,i,mkApp proof h]

partial def exactCoverNormalizedAssemble (formula : Expr) (metadata : Array Json) (start : ℕ)
    (D C M hM hne hroot hlower : Expr) : MetaM (Expr × ℕ) := do
  let val ← mkAppM ``ExactCoverData.valuation #[D,M]
  let parameters := #[M,hM,hne,hroot,hlower]
  if formula.isAppOfArity ``Sat.Fmla.and 2 then
    let args := formula.getAppArgs
    let (left,next) ← exactCoverNormalizedAssemble args[0]! metadata start D C M hM hne hroot hlower
    let (right,next) ← exactCoverNormalizedAssemble args[1]! metadata next D C M hM hne hroot hlower
    let proof := mkApp5 (Lean.mkConst ``sat_satisfies_and) val args[0]! args[1]! left right
    if next-start ≥ 64 then
      let type := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val formula
      return (← exactCoverSeal parameters type proof,next)
    return (proof,next)
  else if formula.isAppOfArity ``Sat.Fmla.one 1 then
    if start ≥ metadata.size then throwError "normalized exact-cover metadata ended early"
    let proof ← exactCoverNormalizedClause metadata[start]! D C M hM hne hroot hlower
    return (mkApp3 (Lean.mkConst ``sat_satisfies_one) val formula.appArg! proof,start+1)
  else throwError "unexpected normalized exact-cover CNF shape"

elab "exact_cover_sat_normalized " cert:term:max metadata:term:max D:term:max C:term:max
    M:term:max hM:term:max hne:term:max hroot:term:max hlower:term:max : tactic => withMainContext do
  let cert ← Tactic.elabTerm cert none
  let D ← Tactic.elabTerm D none
  let C ← Tactic.elabTerm C none
  let M ← Tactic.elabTerm M none
  let hM ← Tactic.elabTerm hM none
  let hne ← Tactic.elabTerm hne none
  let hroot ← Tactic.elabTerm hroot none
  let hlower ← Tactic.elabTerm hlower none
  let source ← unsafe evalTerm String (Lean.mkConst ``String) metadata
  let .ok json := Json.parse source | throwError "invalid normalized exact-cover metadata"
  let .ok metadata := json.getArr? | throwError "normalized exact-cover metadata is not an array"
  let ctx := (← inferType cert).getAppArgs[0]!
  let some formula := (← getConstInfo ctx.constName!).value?
    | throwError "missing normalized exact-cover CNF definition"
  let (proof,used) ← exactCoverNormalizedAssemble formula metadata 0 D C M hM hne hroot hlower
  if used != metadata.size then throwError "unused normalized exact-cover metadata"
  let val ← mkAppM ``ExactCoverData.valuation #[D,M]
  let expected := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val ctx
  unless ← isDefEq (← inferType proof) expected do
    throwError "normalized exact-cover semantics differ from the certified CNF"
  (← getMainGoal).assign (mkApp2 cert val proof)
  replaceMainGoal []

end RigidGHZ.Finite
