module

public import RigidGHZ.Finite.ExactCoverSAT

/-! Untrusted metadata chooses instances of the proved exact-cover semantic
lemmas. The kernel checks each instance against the literal certified CNF. -/

public meta section
namespace RigidGHZ.Finite
open Lean Meta Elab Term Tactic Qq

def exactCoverFin (bound value : ℕ) : MetaM Expr := do
  let b : Q(ℕ) := toExpr bound
  let v : Q(ℕ) := toExpr value
  let h ← mkDecideProofQ q($v < $b)
  return mkApp3 (Lean.mkConst ``Fin.mk) b v h

def exactCoverClauseProof (entry : Json) (D C M hM hne : Expr) : MetaM Expr := do
  let .ok args := entry.getArr? | throwError "expected exact-cover metadata array"
  let .ok kind := args[0]!.getStr? | throwError "expected exact-cover clause kind"
  let ty ← inferType D
  let params := ty.getAppArgs
  let some n ← Meta.evalNat params[params.size - 3]!
    | throwError "exact-cover vertex index size is not concrete"
  let some e ← Meta.evalNat params[params.size - 2]!
    | throwError "exact-cover edge index size is not concrete"
  let some d ← Meta.evalNat params[params.size - 1]!
    | throwError "exact-cover row index size is not concrete"
  let arg (i : ℕ) : MetaM ℕ := do
    let .ok value := args[i]!.getNat? | throwError "expected numeric clause parameter"
    return value
  let fin (bound i : ℕ) : MetaM Expr := do exactCoverFin bound (← arg i)
  match kind with
  | "cover" => mkAppM ``exactCover_cover #[D,C,M,hM,← fin n 1]
  | "exclude" => mkAppM ``exactCover_exclude #[D,C,M,hM,hne,← fin d 1]
  | "conflict" =>
    let proof ← mkAppM ``exactCover_conflict #[D,C,M,hM,← fin e 1,← fin e 2,← fin n 3]
    let .forallE _ domain _ _ ← whnf (← inferType proof)
      | throwError "unexpected exact-cover conflict lemma type"
    let domain : Q(Prop) := domain
    let h ← mkDecideProofQ domain
    return mkApp proof h
  | _ => throwError "unknown exact-cover clause kind {kind}"

def exactCoverSeal (parameters : Array Expr) (type proof : Expr) : MetaM Expr := do
  let type ← mkForallFVars parameters type
  let proof ← instantiateMVars proof
  let proof ← mkLambdaFVars parameters proof
  let name ← mkAuxDeclName `exactCoverSemantic
  withOptions (fun o => o.setBool `Elab.async false) do
    addDecl <| Declaration.thmDecl {name,levelParams := [],type,value := proof}
  resetCache
  return mkAppN (Lean.mkConst name) parameters

partial def exactCoverAssemble (formula : Expr) (metadata : Array Json) (start : ℕ)
    (D C M hM hne : Expr) : MetaM (Expr × ℕ) := do
  let val ← mkAppM ``ExactCoverData.valuation #[D,M]
  let parameters := #[M,hM,hne]
  if formula.isAppOfArity ``Sat.Fmla.and 2 then
    let args := formula.getAppArgs
    let (left,next) ← exactCoverAssemble args[0]! metadata start D C M hM hne
    let (right,next) ← exactCoverAssemble args[1]! metadata next D C M hM hne
    let proof := mkApp5 (Lean.mkConst ``sat_satisfies_and) val args[0]! args[1]! left right
    if next - start ≥ 64 then
      let type := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val formula
      return (← exactCoverSeal parameters type proof,next)
    return (proof,next)
  else if formula.isAppOfArity ``Sat.Fmla.one 1 then
    if start ≥ metadata.size then throwError "exact-cover metadata ended early"
    let proof ← exactCoverClauseProof metadata[start]! D C M hM hne
    let clause := formula.appArg!
    return (mkApp3 (Lean.mkConst ``sat_satisfies_one) val clause proof,start+1)
  else throwError "unexpected exact-cover CNF conjunction shape"

elab "exact_cover_sat " cert:term:max metadata:term:max D:term:max C:term:max
    M:term:max hM:term:max hne:term:max : tactic => withMainContext do
  let cert ← Tactic.elabTerm cert none
  let D ← Tactic.elabTerm D none
  let C ← Tactic.elabTerm C none
  let M ← Tactic.elabTerm M none
  let hM ← Tactic.elabTerm hM none
  let hne ← Tactic.elabTerm hne none
  let source ← unsafe evalTerm String (Lean.mkConst ``String) metadata
  let .ok json := Json.parse source | throwError "invalid exact-cover metadata JSON"
  let .ok metadata := json.getArr? | throwError "exact-cover metadata is not an array"
  let certType ← inferType cert
  let ctx := certType.getAppArgs[0]!
  let some formula := (← getConstInfo ctx.constName!).value?
    | throwError "missing exact-cover CNF definition"
  let (proof,used) ← exactCoverAssemble formula metadata 0 D C M hM hne
  if used != metadata.size then throwError "unused exact-cover metadata"
  let val ← mkAppM ``ExactCoverData.valuation #[D,M]
  let expected := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val ctx
  unless ← isDefEq (← inferType proof) expected do
    throwError "exact-cover semantic clauses differ from the certified CNF"
  (← getMainGoal).assign (mkApp2 cert val proof)
  replaceMainGoal []

end RigidGHZ.Finite
