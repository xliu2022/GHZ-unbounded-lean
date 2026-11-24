module

public import Mathlib.Tactic.Sat.FromLRAT
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic

@[expose] public section
namespace RigidGHZ.Finite

/-- Satisfying two CNF components satisfies their conjunction. -/
theorem sat_satisfies_and {v : Sat.Valuation} {A B : Sat.Fmla}
    (ha : v.satisfies_fmla A) (hb : v.satisfies_fmla B) :
    v.satisfies_fmla (Sat.Fmla.and A B) := by
  refine ⟨fun c hc => ?_⟩
  rcases List.mem_append.mp hc with h | h
  · exact ha.prop c h
  · exact hb.prop c h

 theorem sat_satisfies_one {v : Sat.Valuation} {c : Sat.Clause}
    (h : v.satisfies c) : v.satisfies_fmla (Sat.Fmla.one c) := by
  refine ⟨fun c' hc => ?_⟩
  have heq : c' = c := by simpa only [Sat.Fmla.one, List.mem_singleton] using hc
  simpa only [heq] using h

 theorem sat_positive_list {v : Sat.Valuation} {xs : List ℕ}
    (h : ∃ i ∈ xs, v i) : v.satisfies (xs.map Sat.Literal.pos) := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    intro ha
    obtain ⟨i,hi,hv⟩ := h
    rcases List.mem_cons.mp hi with rfl | hi
    · exact False.elim (ha hv)
    · exact ih ⟨i,hi,hv⟩

/-- Count present inputs before a given position. -/
def prefixCount (P : Fin 28 → Prop) [DecidablePred P] (i : ℕ) : ℕ :=
  (Finset.univ.filter (fun j : Fin 28 => j.val < i ∧ P j)).card

 theorem prefixCount_zero (P : Fin 28 → Prop) [DecidablePred P] : prefixCount P 0 = 0 := by
  simp [prefixCount]

 theorem prefixCount_full (P : Fin 28 → Prop) [DecidablePred P] :
    prefixCount P 28 = (Finset.univ.filter P).card := by
  simp [prefixCount]

 theorem prefixCount_step (P : Fin 28 → Prop) [DecidablePred P] (i : Fin 28) :
    prefixCount P (i.val + 1) = prefixCount P i.val + if P i then 1 else 0 := by
  let S := Finset.univ.filter (fun j : Fin 28 => j.val < i.val ∧ P j)
  have hi : i ∉ S := by simp [S]
  by_cases hp : P i
  · have heq : Finset.univ.filter (fun j : Fin 28 => j.val < i.val + 1 ∧ P j) = insert i S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, S]
      constructor
      · rintro ⟨hj,hp'⟩
        by_cases hji : j = i
        · exact Or.inl hji
        · exact Or.inr ⟨by have hv : j.val ≠ i.val := fun h => hji (Fin.ext h); omega, hp'⟩
      · rintro (rfl | ⟨hj,hp'⟩)
        · exact ⟨by omega, hp⟩
        · exact ⟨by omega, hp'⟩
    change (Finset.univ.filter (fun j : Fin 28 => j.val < i.val + 1 ∧ P j)).card = S.card + _
    rw [heq, Finset.card_insert_of_notMem hi]
    simp [hp]
  · have heq : Finset.univ.filter (fun j : Fin 28 => j.val < i.val + 1 ∧ P j) = S := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, S]
      constructor
      · rintro ⟨hj,hp'⟩
        have hji : j ≠ i := by rintro rfl; exact hp hp'
        exact ⟨by have hv : j.val ≠ i.val := fun h => hji (Fin.ext h); omega, hp'⟩
      · exact fun ⟨hj,hp'⟩ => ⟨by omega,hp'⟩
    change (Finset.univ.filter (fun j : Fin 28 => j.val < i.val + 1 ∧ P j)).card = S.card + _
    rw [heq]
    simp [hp]

 theorem prefixThreshold_step (P : Fin 28 → Prop) [DecidablePred P]
    (i : Fin 28) (k : ℕ) :
    k + 1 ≤ prefixCount P (i.val + 1) ↔
      k + 1 ≤ prefixCount P i.val ∨ (P i ∧ k ≤ prefixCount P i.val) := by
  rw [prefixCount_step]
  by_cases hp : P i <;> simp only [hp, if_true, if_false, true_and, false_and, or_false] <;> omega

end RigidGHZ.Finite

public meta section
open Lean Elab Command Meta Term

/-- Reconstruct each LRAT inference as a separate checked theorem. Naming
intermediate clauses bounds kernel memory and preserves sharing in the exported
proof, including for the larger nine-vertex certificates. -/
def checkedLRAT (cnf lrat : String) (name : Name) : MetaM (Expr × Expr) := do
  let .success _ (_, arr) := Mathlib.Tactic.Sat.Parser.parseDimacs ⟨_,cnf.startPos⟩
    | throwError "parse CNF failed"
  if arr.isEmpty then throwError "empty CNF"
  let ctx' := Mathlib.Tactic.Sat.buildConj arr 0 arr.size
  let ctxName ← mkAuxDeclName (name ++ `ctx)
  addDecl <| Declaration.defnDecl {
    name := ctxName, levelParams := [], type := mkConst ``Sat.Fmla,
    value := ctx', hints := ReducibilityHints.regular 0, safety := .safe }
  let ctx := Lean.mkConst ctxName
  let .success _ steps := Mathlib.Tactic.Sat.Parser.parseLRAT ⟨_,lrat.startPos⟩
    | throwError "parse LRAT failed"
  let p := mkApp (mkConst ``Sat.Fmla.subsumes_self) ctx
  let mut db := (Mathlib.Tactic.Sat.buildClauses arr ctx 0 arr.size ctx' p default).2
  for step in steps do
    match step with
    | .del ids => db := ids.foldl (·.erase ·) db
    | .add i ns pf =>
      -- Name original clauses on first use as well. Rechecking an inline
      -- projection through the large CNF at every RUP step wastes kernel memory.
      for ref in pf do
        let id := ref.natAbs
        let some cl := db[id]? | throwError "missing LRAT premise {id}"
        unless cl.proof.isConst do
          let baseName ← mkAuxDeclName (name ++ `premise)
          addDecl <| Declaration.thmDecl {
            name := baseName, levelParams := [],
            type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx cl.expr, value := cl.proof }
          resetCache
          db := db.insert id { cl with proof := Lean.mkConst baseName }
      let clause := Mathlib.Tactic.Sat.buildClause ns
      let .ok proof := Mathlib.Tactic.Sat.buildProofStep db ns pf ctx clause
        | throwError "invalid LRAT inference {i}"
      let declName ← mkAuxDeclName (name ++ `step)
      addDecl <| Declaration.thmDecl {
        name := declName, levelParams := [],
        type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx clause, value := proof }
      resetCache
      let proof := Lean.mkConst declName
      if ns.isEmpty then return (ctx,proof)
      db := db.insert i { lits := ns, expr := clause, proof }
  throwError "LRAT certificate does not end in contradiction"

/-- Import an LRAT proof by reconstructing ordinary proof terms in the Lean
kernel. File readers and the SAT solver are untrusted. No native reduction axiom
is used: every inference passes the ordinary declaration checker. -/
elab "kernel_lrat " n:ident cnf:term:max lrat:term:max : command => do
  liftTermElabM do
    let name := (← getCurrNamespace) ++ n.getId
    let cnf ← unsafe evalTerm String (mkConst ``String) cnf
    let lrat ← unsafe evalTerm String (mkConst ``String) lrat
    let (ctx, proof) ← checkedLRAT cnf lrat name
    addDecl <| Declaration.thmDecl {
      name, levelParams := [],
      type := mkApp2 (mkConst ``Sat.Fmla.proof) ctx (Mathlib.Tactic.Sat.buildClause #[]),
      value := proof }
