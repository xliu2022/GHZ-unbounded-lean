module

public import RigidGHZ.Finite.NineSATModel

/-! The clause metadata only guides proof assembly. Each generated application
is an instance of a proved semantic lemma. The kernel checks that its clause is
exactly the clause in the LRAT theorem's CNF. -/

public meta section
namespace RigidGHZ.Finite
open Lean Meta Elab Term Tactic Qq

 def nineSatProgress (message : String) : MetaM Unit := do
  if let some path ← IO.getEnv "RIGID_GHZ_SAT_PROGRESS" then
    IO.FS.writeFile path message

 def nineSatFin (bound value : ℕ) : MetaM Expr := do
  let b : Q(ℕ) := toExpr bound
  let v : Q(ℕ) := toExpr value
  let h ← mkDecideProofQ q($v < $b)
  return mkApp3 (Lean.mkConst ``Fin.mk) b v h

 def nineSatClauseProof (entry : Json) (H hU F hnorm : Expr) (hmax : Option Expr) (supplied : Array Expr) : MetaM Expr := do
  let .ok args := entry.getArr? | throwError "expected clause metadata array"
  let .ok kind := args[0]!.getStr? | throwError "expected clause kind"
  let arg (i : ℕ) : MetaM ℕ := do
    let .ok n := args[i]!.getNat? | throwError "expected numeric clause parameter"
    return n
  let fin (bound i : ℕ) : MetaM Expr := do nineSatFin bound (←arg i)
  match kind with
  | "forward" => mkAppM ``nineSAT_forward #[H,←fin 280 1,←fin 3 2]
  | "backward" => mkAppM ``nineSAT_backward #[H,←fin 280 1]
  | "cover" => mkAppM ``nineSAT_cover #[hU,F,←fin 84 1]
  | "conflict" => mkAppM ``nineSAT_conflict #[F,←fin 84 1,←fin 45 2]
  | "zero" => mkAppM ``nineSAT_zero #[H,←fin 9 1,←fin 29 2]
  | "empty" => mkAppM ``nineSAT_empty #[H,←fin 9 1,←fin 15 2]
  | "step1" => mkAppM ``nineSAT_step1 #[H,←fin 9 1,←fin 28 2,←fin 15 3]
  | "step2" => mkAppM ``nineSAT_step2 #[H,←fin 9 1,←fin 28 2,←fin 15 3]
  | "step3" => mkAppM ``nineSAT_step3 #[H,←fin 9 1,←fin 28 2,←fin 15 3]
  | "step4" => mkAppM ``nineSAT_step4 #[H,←fin 9 1,←fin 28 2,←fin 15 3]
  | "lower" => mkAppM ``nineSAT_lower #[hU,F,←fin 9 1]
  | "upper" => mkAppM ``nineSAT_upper #[hU,F,←fin 9 1]
  | "given" =>
    let i ← arg 1
    if i ≥ supplied.size then throwError "missing supplied edge"
    mkAppM ``nineSAT_given #[←fin 84 2,supplied[i]!]
  | "fan" =>
    let some hm := hmax | throwError "missing codegree bound for fan clause"
    mkAppM ``nineSAT_fan #[hm,←fin 756 1]
  | "normpos" =>
    let n : Q(ℕ) := toExpr (←arg 1)
    let k : Q(ℕ) := (←inferType hnorm).getAppArgs[1]!
    let h ← mkDecideProofQ q($n < $k)
    mkAppM ``nineSAT_normpos #[hnorm,←fin 7 1,h]
  | "normneg" =>
    let n : Q(ℕ) := toExpr (←arg 1)
    let k : Q(ℕ) := (←inferType hnorm).getAppArgs[1]!
    let h ← mkDecideProofQ q($k ≤ $n)
    mkAppM ``nineSAT_normneg #[hnorm,←fin 7 1,h]
  | _ => throwError "unknown clause kind {kind}"

 /-- Check and name a semantic subproof before composing it with other clauses.
 The expected type uses the literal clause from the certified CNF. -/
 def nineSatSeal (parameters : Array Expr) (type proof : Expr) : MetaM Expr := do
  let type ← mkForallFVars parameters type
  let proof ← instantiateMVars proof
  let proof ← mkLambdaFVars parameters proof
  let name ← mkAuxDeclName `nineSemantic
  withOptions (fun o => o.setBool `Elab.async false) do
    addDecl <| Declaration.thmDecl {name,levelParams := [],type,value := proof}
  resetCache
  return mkAppN (Lean.mkConst name) parameters

 partial def nineSatAssemble (formula : Expr) (metadata : Array Json) (start : ℕ)
    (H hU F hnorm : Expr) (hmax : Option Expr) (supplied : Array Expr) : MetaM (Expr × ℕ) := do
  let val := mkApp (Lean.mkConst ``nineSATValuation) H
  let parameters := #[H,hU,F,hnorm] ++ hmax.toArray ++ supplied
  if formula.isAppOfArity ``Sat.Fmla.and 2 then
    let args := formula.getAppArgs
    let (left,next) ← nineSatAssemble args[0]! metadata start H hU F hnorm hmax supplied
    let (right,next) ← nineSatAssemble args[1]! metadata next H hU F hnorm hmax supplied
    let proof := mkApp5 (Lean.mkConst ``sat_satisfies_and) val args[0]! args[1]! left right
    if next - start ≥ 64 then
      let type := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val formula
      return (←nineSatSeal parameters type proof,next)
    return (proof,next)
  else if formula.isAppOfArity ``Sat.Fmla.one 1 then
    if start ≥ metadata.size then throwError "clause metadata ended early"
    nineSatProgress s!"Building semantic clause {start}/{metadata.size}"
    let proof ← nineSatClauseProof metadata[start]! H hU F hnorm hmax supplied
    nineSatProgress s!"Checking semantic clause {start}/{metadata.size}"
    let clause := formula.appArg!
    -- The enclosing group is checked and named by `nineSatSeal`. Keeping a
    -- small group together lets the kernel reuse its conversion cache.
    return (mkApp3 (Lean.mkConst ``sat_satisfies_one) val clause proof,start+1)
  else throwError "unexpected CNF conjunction shape"

 def nineSatFinish (cert metaInput Hst hUst Fst normst : Syntax) (maxst : Option Syntax) (givenst : Array Syntax) : TacticM Unit := withMainContext do
  nineSatProgress "Preparing certified CNF semantics"
  let cert ← Tactic.elabTerm cert none
  let H ← Tactic.elabTerm Hst none
  let hU ← Tactic.elabTerm hUst none
  let F ← Tactic.elabTerm Fst none
  let hnorm ← Tactic.elabTerm normst none
  let hmax ← maxst.mapM (fun st => Tactic.elabTerm st none)
  let supplied ← givenst.mapM (fun st => Tactic.elabTerm st none)
  nineSatProgress "Reading clause metadata"
  let metaString ← unsafe evalTerm String (Lean.mkConst ``String) metaInput
  let .ok json := Json.parse metaString | throwError "invalid clause metadata JSON"
  let .ok metadata := json.getArr? | throwError "clause metadata is not an array"
  let certType ← inferType cert
  let ctx := certType.getAppArgs[0]!
  let some formula := (←getConstInfo ctx.constName!).value? | throwError "missing CNF definition"
  nineSatProgress "Starting semantic clause checks"
  let (proof,used) ← nineSatAssemble formula metadata 0 H hU F hnorm hmax supplied
  if used != metadata.size then throwError "unused clause metadata"
  let val := mkApp (Lean.mkConst ``nineSATValuation) H
  let expected := mkApp2 (Lean.mkConst ``Sat.Valuation.satisfies_fmla) val ctx
  unless ←isDefEq (←inferType proof) expected do
    throwError "assembled semantic clauses differ from the certified CNF"
  let result := mkApp2 cert val proof
  (←getMainGoal).assign result
  replaceMainGoal []

elab "nine_sat_finish " cert:term:max metaInput:term:max H:term:max hU:term:max F:term:max hnorm:term:max : tactic =>
  nineSatFinish cert metaInput H hU F hnorm none #[]

elab "nine_sat_finish_max " cert:term:max metaInput:term:max H:term:max hU:term:max F:term:max hnorm:term:max hmax:term:max : tactic =>
  nineSatFinish cert metaInput H hU F hnorm (some hmax) #[]

elab "nine_sat_finish_edges " cert:term:max metaInput:term:max H:term:max hU:term:max F:term:max hnorm:term:max h0:term:max h1:term:max : tactic =>
  nineSatFinish cert metaInput H hU F hnorm none #[h0,h1]

elab "nine_sat_finish_max_edges " cert:term:max metaInput:term:max H:term:max hU:term:max F:term:max hnorm:term:max hmax:term:max h0:term:max h1:term:max : tactic =>
  nineSatFinish cert metaInput H hU F hnorm (some hmax) #[h0,h1]

end RigidGHZ.Finite
