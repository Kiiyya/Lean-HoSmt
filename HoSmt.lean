import Lean
import Lean.Data
import HoSmt.Translation
import HoSmt.TPTP
import HoSmt.System
import HoSmt.Util
import HoSmt.Options
-- import HoSmt.Reconstruction
import HoSmt.Decode.Alethe2

open HoSmt.TPTP
open HoSmt.Util
open Lean Elab Term Command Tactic Expr HoSmt.Translation Std

namespace HoSmt

initialize Lean.registerTraceClass `HoSmt
initialize Lean.registerTraceClass `HoSmt.debug
initialize Lean.registerTraceClass `HoSmt.lctxLift
initialize Lean.registerTraceClass `HoSmt.bench

/-- Lifts an expression to its own definition. -/
def defineExpression (expr : Expr) : MetaM Name := do
  let ty <- Meta.inferType expr
  let levelParams := collectLevelParams (collectLevelParams {} expr) ty |>.params
  let decl : DefinitionVal := {
    name := `aux ++ (<- mkFreshId),
    levelParams := levelParams.toList,
    type := ty,
    value := expr,
    hints := ReducibilityHints.abbrev,
    safety := DefinitionSafety.safe,
  }
  addDecl (Declaration.defnDecl decl)
  return decl.name

/-- Makes the list of names in the lean infoview clickable, and gives you type info when you hover over them. -/
def namesWithMData (set : HashSet Name) : TacticM MessageData := do
  let inner <- set.foldM (fun md name => do
    let some ci := (<- getEnv).find? name | panic! ""
    return m!"{Expr.const name (ci.levelParams.map Level.param)}, {md}"
  ) m!""
  return m!"\{{inner}}"

inductive SmtResult
| proof : String -> SmtResult
| contra : String -> SmtResult
/-- Timeout, gave up, etc. -/
| gaveUp : Option String -> SmtResult

def runSMT (tptp : String) : CoreM SmtResult := do
  let result <- System.cmd_cvc5 tptp
  -- trace[HoSmt] "CVC5 returned: {result.stdout}"
  if result.stdout.startsWith "unsat" then
    return SmtResult.proof result.stdout
  else if result.stdout.startsWith "sat" then
    return SmtResult.contra result.stdout
  else if result.stdout == "" then -- timeout
    return .gaveUp none
  else if result.stdout.startsWith "unknown" then
    return .gaveUp result.stdout
  else if result.stdout.startsWith "(error" then
    throwError result.stdout
  else
    throwError "smt solver produced unknown output."

/-- Any env modifications that happen inside `f` will be reset afterwards. -/
def withEnvSandbox (f : TacticM α) : TacticM α := do
  let oldEnv <- getEnv
  try f
  finally setEnv oldEnv

/--
  Given a context such as `x : α ⊢ ?g : P`, lifts `x : α` into a new environment item,
  and in `P` replaces the fvar `x` with the freshly added env item.

  - For `x : Type`, adds `axiom x : Type`
  - For `x : Nat`, adds `axiom x : Nat`
  - For `x : Nat := 1234`, adds `def x : Nat := 1234`
-/
partial def liftLCtxToEnv (goal : MVarId) : TacticM MVarId := goal.withContext do
  let lctx <- getLCtx
  let fvarIds <- lctx.getFVarIds.filterM (fun fv => do return !(<- fv.getDecl).isAuxDecl) -- filter out recursive def fvars (should always be first in lctx iirc, so shouldn't depend on other fvars)

  -- implemented recursively, with this being the termination condition:
  let some fvarId := fvarIds.get? 0
    | return goal

  let ldecl := lctx.getFVar! (.fvar fvarId)
  let name := ldecl.userName ++ (<- mkFreshId)
  let (decl, levelParams, value?) <- match ldecl with
    | .cdecl _ _ _ type _ _ => do
      let decl : AxiomVal := {
        name
        levelParams := Lean.collectLevelParams {} type |>.params.toList
        type := <- instantiateMVars type
        isUnsafe := false
      }
      pure (Declaration.axiomDecl decl, decl.levelParams, none)
    | .ldecl _ _ _ type value _ _ => do
      let decl : DefinitionVal := {
        name
        levelParams := (Lean.collectLevelParams (Lean.collectLevelParams {} value) type) |>.params.toList
        type := <- instantiateMVars type
        value := <- instantiateMVars value
        hints := ReducibilityHints.abbrev
        safety := .safe
      }
      pure (Declaration.defnDecl decl, decl.levelParams, some value)

  let log
  | .ok () => return m!"Lifting {ldecl.userName} into its own environment item {name} with type {ldecl.type} and value {value?} ~~> ok"
  | .error err => return m!"Lifting {ldecl.userName} into its own environment item {name} with type {ldecl.type} and value {value?} ~~> {err.toMessageData}"
  withTraceNode `HoSmt.lctxLift log do
    addDecl decl

  let const := (.const name (<- Meta.mkFreshLevelMVars levelParams.length)) -- TODO: elab levelParam mvars somehow
  let goalType' := (<- goal.getType).replaceFVarId fvarId const
  let _throwaway <- Meta.inferType goalType' -- not sure if the right way, but isDefEq wouldn't make sense here I think?
  let goalType' <- instantiateMVars goalType'

  let lctx' := lctx.replaceFVarId fvarId const
  admitGoal goal -- no proof reconstruction yet.

  Meta.withLCtx lctx' (<- Meta.getLocalInstances) do
    let goal' <- Meta.mkFreshExprMVar (some goalType')
    trace[HoSmt.lctxLift] "After lifting, the new goal is{goal'.mvarId!}"
    replaceMainGoal [goal'.mvarId!]
    liftLCtxToEnv goal'.mvarId! -- recurse: next lctx decl

/--
  Translate the goal to TPTP and any constants reachable from it, recursively.
  Also include auxiliary constants in `auxes`, e.g. from lemma selection.
-/
def leanToTPTP (auxes : Array Name) : TacticM (String × MVarId) := do
  -- # Lift LCtx into their own env items
  let goal <- liftLCtxToEnv (<- getMainGoal)
  trace[HoSmt] "leanToTPTP goal is {Expr.mvar goal}"

  goal.withContext do
    -- # Translate (most heavy lifting happens here)
    let (goal', auxes', equations) <- TransM.run do
      let goal' <- Translation.translateGoal goal
      let auxes' <- auxes.mapM Translation.translateConst
      return (goal', auxes', (<- get).equations)

    trace[HoSmt] m!"After translation goal is {goal'}"

    -- # Generate TPTP
    let tptp <- EncodeM.run equations do
      auxes'.forM TPTP.addConst
      TPTP.addGoal goal'
    return (tptp, goal')

open HoSmt.Decode.Alethe2 in
def hammer (auxes : Array Name) : TacticM Unit := do
  let (tptp, goal') <- leanToTPTP auxes
  trace[HoSmt] tptp

  -- # Run CVC5
  match <- runSMT tptp with
  | .proof prf_string => do
    logInfo m!"PROOF:\n{prf_string}"

    -- Just for debugging/testing, you can disable proof reconstruction with an option entirely:
    unless HoSmt.reconstruct.get (<- getOptions) do
      admitGoal goal'
      return

    withAlethe2OpenDecl do
      let `(aproof| unsat $cmds*) <- IO.ofExcept <| Parser.runParserCategory (<- getEnv) `aproof prf_string
        | throwError "failed to parse alethe proof"
      smtHarness cmds

  | .contra contra => do
    throwError "CONTRADICTON:\n{contra}"
  | .gaveUp msg => do
    if HoSmt.shouldTranslate.get (<- getOptions) then
      admitGoal goal'
      logInfo "GAVE UP (but translation successful)"
    else
      throwError "GAVE UP{if msg.isSome then ": \n" else ""}{msg}"

syntax smtArgs := "[" (ident <|> term),* "]"

elab "smt " auxes?:(smtArgs)? : tactic => do
  trace[HoSmt] "Original goal mvar is {Expr.mvar (<- getMainGoal)}"

  -- Add auxiliary lemmas explicitly provided by the user.
  let auxes <- auxes? |>.map (fun x => x.raw[1]) |>.map Syntax.getSepArgs |>.getD #[] |>.mapM fun aux => do
    if let .ident _ _ th .. := aux then return th
    let aux <- Tactic.elabTerm aux none
    if let some (name, _) := aux.const? then return name
    else defineExpression aux

  withEnvSandbox do
    hammer auxes

elab "#reprove " name:ident auxes?:(smtArgs)? : command => do
  Command.liftTermElabM do
    let .ident _ _ th .. := name.raw | throwError "not an ident"
    let some (.thmInfo info) := (<- getEnv).find? th | throwError "no such theorem"

    -- Add auxiliary lemmas explicitly provided by the user.
    let auxes <- auxes? |>.map (fun x => x.raw[1]) |>.map Syntax.getSepArgs |>.getD #[] |>.mapM fun aux => do
      if let .ident _ _ th .. := aux then return th
      let aux <- elabTerm aux none
      if let some (name, _) := aux.const? then return name
      else defineExpression aux

    let goal <- Meta.mkFreshExprMVar (some info.type)
      let _outputGoals <- Tactic.run (goal.mvarId!) do
        withEnvSandbox do
          hammer auxes

-- open Lean Meta in
-- elab "#translate" name:ident : command => do
--   Command.liftTermElabM do
--     let .ident _ _ n .. := name.raw | throwError "not an ident"
--     let some ci := (<- getEnv).find? n | throwError "no such constant"
--     let goal <- Meta.mkFreshExprMVar none
--     let goals' <- Tactic.run (goal.mvarId!) do
--       goal.mvarId!.withContext do
--         TransM.run do
--           let const' <- Translation.translateConst n
--           logInfo m!"{const'}"

end HoSmt
