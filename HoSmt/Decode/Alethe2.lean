import Lean
import Qq
import Duper.Tactic
import HoSmt.Decode.Rules

namespace HoSmt.Decode.Alethe2

/-! # Alethe2 Parser and Elaborator
  Alethe2 is a textual proof format returned by CVC5.
  https://verit.loria.fr/documentation/alethe-spec.pdf

  1. We use Lean's parser, which has a nice side-effect of being able to directly write (or copy-paste)
     Alethe2 proofs into Lean files.
  2. Then we elaborate the parsed syntax into `Lean.Expr`.
-/

open Lean Elab Term Meta Tactic

/-- Just using logInfo causes extreme performance problems for some reason. -/
def loggInfo (e : MessageData) : TacticM Unit := do
  logInfo e

/-- Just using logInfo causes extreme performance problems for some reason. -/
def loggInfoAt (stx : Syntax) (e : MessageData) : TacticM Unit := do
  logInfoAt stx e

/-- This is very hacky, but works. -/
def withAlethe2OpenDecl (m : TacticM Unit) : TacticM Unit := do
  try
    pushScope
    let openDecls ← elabOpenDecl (<- `(Lean.Parser.Command.openDecl| HoSmt.Decode.Alethe2))
    withTheReader Core.Context (fun ctx => { ctx with openDecls := openDecls }) do
      m
  finally
    popScope

open Qq

declare_syntax_cat aop
scoped syntax "not " : aop
scoped syntax "and " : aop
scoped syntax "or " : aop
scoped syntax "=> " : aop
scoped syntax "= " : aop
scoped syntax "@ " : aop
scoped syntax "cl " : aop

/-- For example `(x Bool)` -/
declare_syntax_cat abinder
scoped syntax "(" ident ident ")" : abinder

/-- For example `((x Bool) (y Nat))` -/
declare_syntax_cat abinders
scoped syntax "(" abinder* ")" : abinders

declare_syntax_cat aexpr
scoped syntax num : aexpr
scoped syntax ident : aexpr
scoped syntax "(" aop aexpr* ")" : aexpr
scoped syntax "(" "forall" abinders aexpr ")" : aexpr

partial def elabAExpr (ae : TSyntax `aexpr) : TermElabM Expr := do
  let ret <- withRef ae go
  addTermInfo' ae ret
  return ret
where go := do
  match ae with
  | `(aexpr| $n:num) => elabTerm n q(Nat)
  | `(aexpr| Bool) => do
    return q(Prop)
  | `(aexpr| $id:ident) =>
    if let some decl := (<- getLCtx).findFromUserName? id.getId then
      return decl.toExpr
    -- Meta.mkConstWithFreshMVarLevels id.getId
    match id.getId with
    | `false => return q(False)
    | `true => return q(True)
    | `glob_Nat => return q(Nat)
    | `glob_Nat_succ => return q(Nat.succ)
    | `glob_Nat_zero => return q(Nat.zero)
    | _ => throwError "Unknown identifier {id} (note: looking up from Environment not yet supported)"
  | `(aexpr| (@ $f:aexpr $a:aexpr)) =>
    let f <- elabAExpr f
    let a <- elabAExpr a
    return Expr.app f a
  | `(aexpr| (=%$tk $a:aexpr $b:aexpr)) =>
    let a <- elabAExpr a
    let b <- elabAExpr b
    let app <- mkAppM ``Eq #[a, b]
    addTermInfo' tk app.getAppFn
    return app
  | `(aexpr| (=> $a:aexpr $b:aexpr)) =>
    let a : Q(Prop) <- elabAExpr a
    let b : Q(Prop) <- elabAExpr b
    return q($a -> $b)
  | `(aexpr| (not%$tk $a)) =>
    addTermInfo' tk (.const ``Not [])
    let a : Q(Prop) <- elabAExpr a
    return q(¬ $a)
  | `(aexpr| (or%$tk $a $b)) =>
    addTermInfo' tk (.const ``Or [])
    let a : Q(Prop) <- elabAExpr a
    let b : Q(Prop) <- elabAExpr b
    return q($a ∨ $b)
  | `(aexpr| (cl%$tk $xs*)) =>
    addTermInfo' tk (.const ``Or []) -- not entirely accurate but whatever :P
    if xs.size > 0 then
      -- We do a bit more effort just to get `a ∨ b ∨ c` instead of `(a ∨ b) ∨ c`.
      let head : Q(Prop) <- elabAExpr (xs[xs.size - 1]!)
      let f (stx : TSyntax `aexpr) (acc : Q(Prop)) : TermElabM Q(Prop) := do
        let elem : Q(Prop) <- elabAExpr stx
        pure q($elem ∨ $acc)
      (xs[0 : xs.size - 1]).foldrM f head
    else
      return q(False)
  | `(aexpr| (forall ($binders*) $body)) =>
    let f  (binder : TSyntax `abinder) (acc : TermElabM Expr): TermElabM Expr := do
      let `(abinder| ($var $type)) := binder
        | withRef binder <| throwError "unknown abinder syntax {binder}"
      let type_expr <- elabAExpr (<- `(aexpr| $type:ident))
      -- let type_type <- inferType type_expr
      addTermInfo' type type_expr
      withLocalDeclD var.getId type_expr fun fv => do 
        addTermInfo' var fv (isBinder := Bool.true)
        acc >>= (mkForallFVars #[fv] .)
    binders.foldr f (elabAExpr body)
  | _ => throwError "AExpr, unknown syntax {ae}"

def elabAExprIdent (ae : TSyntax `ident) : TermElabM Expr := do
  elabAExpr (<- `(aexpr| $ae:ident))

scoped elab "AEXPR " ae:aexpr : term => elabAExpr ae

#check AEXPR true
#check AEXPR (cl)
#check AEXPR (cl true)
#check AEXPR (or false (or false true))
#check AEXPR (cl (= 1 1) (= 2 2) (= 3 3) (= 4 4) (= 5 5))
#check AEXPR (not (forall ((x Bool)) (or false (or (= x true) (= x (not true))))))
#check AEXPR (not (forall ((x Bool) (y Bool)) (or false (or (= y true) (= x (not true))))))
#check AEXPR (not (forall ((x Bool) (y Bool) (z Bool)) (or false (or (= y z) (= x (not true))))))

/-- Either `(:= x y)` or `(:= (x Bool) y)`. -/
declare_syntax_cat aassignment
scoped syntax "(" ":=" (abinder <|> ident) ident ")" : aassignment

declare_syntax_cat acmd
scoped syntax "(" "assume " ident aexpr ")" : acmd
scoped syntax "(" "step " ident aexpr (":rule" ident) (":premises" "(" ident* ")")? ")" : acmd
scoped syntax "(" "anchor " ":step " ident ":args" "(" aassignment* ")" ")" : acmd

declare_syntax_cat aproof
scoped syntax "unsat " acmd* : aproof

def getCommands (prf : TSyntax `aproof) : Except String <| TSyntaxArray `acmd := Id.run do
  let `(aproof| unsat $cmds*) := prf
    | return .error "unexpected syntax"
  return .ok cmds

/-- Alethe2 subproof. -/
structure Subproof where
  /-- Name of the step that will conclude this subproof. -/
  stepName : Name
  /-- `X : Type`. -/
  X : MVarId
  /-- Has type `X -> Prop`. -/
  α : MVarId
  /-- Has type `X -> Prop`. -/
  β : MVarId
  /-- The formula of the concluding step. This is just for convenience, and is `q((∀x : $X, $α x) = (∀x : $X, $β x))`. -/
  φᵢ : Expr
  /-- The subproof goal `Γ, x : X ⊢ prf_σ : α x = β x`. -/
  prf_σ : MVarId
  /-- A subproof pushes variables onto the context. These are those fvars.
    They are valid in the context of `prf_σ`.  -/
  vars : Array Expr
  deriving BEq, Repr

/-- Alethe2 proof reconstruction (well, more like proof elab) state.
  Currently only tracks the subproof stack. -/
structure RecState where
  /-- Alethe2 has subproofs which begin with `(anchor :step X ...)` and end with `(step X ...)`.
  In order to know when the subproof is concluded, we need to remember the step name `X`.
  One added difficulty is that anchor tags do not state the subproof formula, so we need to
  elaborate blind, until we encounter the concluding step. -/
  proofStack : List Subproof := []
  deriving BEq, Repr

/-- Alethe2 proof reconstruction monad. -/
abbrev ATacticM := StateRefT RecState TacticM

def pushSubproof (subproof : Subproof) : ATacticM Unit := do
  modify fun s => { s with proofStack := subproof :: s.proofStack }
def peekStack : ATacticM <| Option Subproof := do
  return (<- get).proofStack.head?
def popSubproof : ATacticM Unit := do
  modify fun
  | ⟨_ :: ps⟩ => ⟨ps⟩
  | s => s

def liftATacticM (m : ATacticM α) : TacticM α := do
  let (a, ⟨proofStack⟩) <- StateRefT'.run m {}
  if proofStack != [] then
    throwError "Still have subproofs on the proof stack."
  return a

def elabAAnchor (cmd : TSyntax `acmd) : ATacticM Unit := do
  let `(acmd| (anchor :step $stepName:ident :args ($assignments*))) := cmd
    | throwError "whoops"
  let mainGoal <- getMainGoal -- Γ ⊢ ?mainGoal : φ   (here φ is for example `False`)

  -- We don't need to fold, as alethe only has simple types.
  let x : Array (Name × Expr) <- assignments.mapM fun ass => withRef ass do
    let `(aassignment| (:= ($var $type) $_var')) := ass
      | throwError "unknown aassignment syntax {ass}"
    let type_expr <- elabAExprIdent type
    addTermInfo' type type_expr -- shouldn't be necessary
    pure (var.getId, type_expr)

  -- We won't know the goal type of this subproof until we hit the corresponding `(step $i $φᵢ ...)`
  -- much later, so we can't know φᵢ now.
  -- However, we know that `φᵢ =?= (∀x : $X, $α x) = (∀x : $X, $β x)`, and once we do get to step i,
  -- we can find values for X, α, and β.

  -- let X : Q(Type) := x[0]!.snd -- for some reason makes quote4 break :/
  let X <- mkFreshExprMVarQ q(Type) (userName := stepName.getId ++ `X)
  if !(<- isDefEq X x[0]!.snd) then throwError "quote4 is broken :("
  let α <- mkFreshExprMVarQ q($X -> Prop) (userName := stepName.getId ++ `α)
  let β <- mkFreshExprMVarQ q($X -> Prop) (userName := stepName.getId ++ `β)
  let φᵢ : Q(Prop) := q((∀x : $X, $α x) = (∀x : $X, $β x))
  let prf_φᵢ : Q($φᵢ) <- mkFreshExprMVarQ q($φᵢ) (userName := stepName.getId) -- Γ ⊢ (∀x:X, α x) = (∀x:X, β x)
  let prf_ψ <- List.head! <$> prf_φᵢ.mvarId!.apply (<- mkAppOptM ``forall_congr #[X, α, β]) -- Γ ⊢ ∀x:X, α x = β x
  let (x_fvar, prf_σ) <- prf_ψ.intro x[0]!.fst -- Γ, x:X ⊢ α x = β x
  let (fvar, mainGoal') <- mainGoal.assert stepName.getId φᵢ prf_φᵢ >>= (·.intro stepName.getId)
  addTermInfo' stepName (Expr.fvar fvar) (isBinder := Bool.true)
  -- addTermInfo' var_syntax x_fvar (isBinder := true)

  replaceMainGoal [mainGoal']
  setGoals (prf_σ :: (<- getGoals)) -- prepend our subgoal σ, making it the main goal.

  -- Now we transformed mainGoal into two new goals:
  -- Γ, x : X ⊢ ?prf_σ : α x = β x     (our subproof goal)
  -- Γ, prf_φᵢ : φᵢ ⊢ ?mainGoal' : φ   (the updated main goal)

  mainGoal'.withContext do
    addTermInfo' stepName (Expr.fvar x_fvar) (isBinder := Bool.true)

  pushSubproof {
    stepName := stepName.getId
    X := X.mvarId!
    α := α.mvarId!
    β := β.mvarId!
    φᵢ := φᵢ
    prf_σ := prf_σ
    vars := #[Expr.fvar x_fvar]
  }

def elabAAssume (cmd : TSyntax `acmd) : ATacticM Unit := do
  let `(acmd| (assume $a_name $α)) := cmd | throwError "whoops"
  /- Before the assume tag we have the goal `Γ ⊢ ?g : ?ψ`.
    We assign `?ψ := α -> ?β` for a new type mvar ?β, then unify. -/
  let α : Q(Prop) <- elabAExpr α
  let β : Q(Prop) <- mkFreshExprMVarQ q(Prop)

  let g <- getMainGoal
  let ψ : Q(Prop) <- g.getType

  -- We call isDefEq, in order to unify `?ψ` stemming from anchors.
  if <- isDefEq ψ q($α -> $β) then
    -- Now our goal is `Γ ⊢ ?g : α -> ?β`.
    let (fvar, g') <- g.intro a_name.getId
    g'.withContext do
      addTermInfo' a_name (.fvar fvar) (isBinder := Bool.true)
    replaceMainGoal [g']
    -- Done, now we have modified the tactic state into `Γ, a : α ⊢ ?g' : ?β` :)
  else
    throwError "At {cmd}, couldn't unify goal type {ψ} with {q($α -> $β)}"

def elabABindStep (cmd : TSyntax `acmd) (subproof : Subproof) : ATacticM Unit := do
  let `(acmd| (step $stepᵢ $stepStxᵢ :rule $rule $[:premises ($ps*)]?)) := cmd | throwError "whoops"
  let parentGoal := (<- getGoals)[1]!
  let φᵢ <- parentGoal.withContext do
    elabAExpr stepStxᵢ

  -- We did all (or most) of the setup in `elabAAnchor` already.
  -- Now we only fill in the metavar holes.
  let lastStep := (<- getLCtx).lastDecl |>.get!
  let some (_, lhs, rhs) := lastStep.type.eq? | throwError "expected equation, got {lastStep.type} instead."
  let α <- mkLambdaFVars subproof.vars lhs
  let β <- mkLambdaFVars subproof.vars rhs
  if !(<- isDefEq (Expr.mvar subproof.α) α) then
    throwError "Can't determine α, since {Expr.mvar subproof.α} and {α} don't unify"
  if !(<- isDefEq (Expr.mvar subproof.β) β) then
    throwError "Can't determine β, since {Expr.mvar subproof.β} and {β} don't unify"
  if !(<- isDefEq φᵢ subproof.φᵢ) then
    throwError "The concluding step formula {φᵢ} is expected to unify with {subproof.φᵢ}"

  evalTactic (<- `(tactic| assumption)) -- should grab the last (sub)step.

def elabAStep (cmd : TSyntax `acmd)  : ATacticM Unit := do
  let `(acmd| (step $stepᵢ $stepStxᵢ :rule $rule $[:premises ($ps*)]?)) := cmd | throwError "whoops"

  let φᵢ : Q(Prop) <- elabAExpr stepStxᵢ -- The formula for the current step i.
  -- This is a normal step. Find a proof for φ.
  let proof : Q($φᵢ) <- mkFreshExprMVarQ q($φᵢ)
  let tac <- match rule.getId with
  -- | `equiv_pos2 => `(tactic| exact equiv_pos2)
  | _ => `(tactic| duper)
  let res : List MVarId <- evalTacticAt tac proof.mvarId!
  let proof : Q($φᵢ) <- instantiateMVars proof
  if proof.hasMVar || !res.isEmpty then
    throwError "Still got mvars in proof for {cmd}. Tactic {tac} returned new goals {res} with proof {proof}"

  -- Add the proved step to the context.
  -- We use `MVarId.define` instead of `MVarId.assert`, so that we get let-declarations.
  let goal' <- (<- getMainGoal).assert stepᵢ.getId φᵢ proof
  let (h, goal'') <- goal'.intro stepᵢ.getId
  goal''.withContext do
    addTermInfo' stepᵢ (.fvar h) (isBinder := Bool.true)
  replaceMainGoal [goal'']

/-- Elab a command such as `(assume a0 φ)`, create a new fvar `a0 : φ`, add it to the context,
  call f, then reset context; in the end produces a function.
  If the command is a `(step ti φ :rule R ...)`, add a let declaration `ti : φ := proof`, where
  `proof` is obtained by some form of rule application or tactic corresponding to `R`.
  For now, we just call `by duper` on everything :). -/
def elabACommand (cmd : TSyntax `acmd) : ATacticM Unit := do
  let mainGoal <- getMainGoal
  mainGoal.withContext <| withRef cmd do
    match cmd with
    | `(acmd| (anchor%$tk :step $i:ident :args ($assignments*))) => elabAAnchor cmd
    | `(acmd| (assume $a_name $α)) => elabAAssume cmd
    | `(acmd| (step $id $ae :rule $rule $[:premises ($ps*)]?)) => do
      -- First check whether this is step concludes a subproof.
      if let (subproof :: _) := (<- get).proofStack then
        if subproof.stepName == id.getId then
          popSubproof
          if rule.getId != "bind" then throwError "currently only 'bind' concluding subproof rules implemented."
          elabABindStep cmd subproof
        else
          elabAStep cmd
      else
        elabAStep cmd
    | _ => throwError "elabACommand: unknown syntax {cmd}"

def mkInitialTacticInfo (stx : Syntax) : ATacticM (ATacticM Info) := do
  let mctxBefore  ← getMCtx
  let goalsBefore ← getUnsolvedGoals
  return mkTacticInfo mctxBefore goalsBefore stx

@[inline] def withTacticInfoContext [inst : MonadLiftT TacticM ATacticM] (stx : Syntax) (x : ATacticM α) : ATacticM α := do
  let xxx : ATacticM Info ← mkInitialTacticInfo stx
  withInfoContext x xxx

def elabACommands (aproof : TSyntaxArray `acmd) : ATacticM Unit := do
  aproof.forM fun (cmd : TSyntax `acmd) => do
    withTacticInfoContext cmd do
      elabACommand cmd
    
theorem smt_harness (h: ¬φ -> True -> False) : φ := by
  apply Classical.byContradiction
  intro not_φ
  exact h not_φ True.intro

def smtHarness (aproof : TSyntaxArray `acmd) : TacticM Unit := withMainContext do
  -- Our goal state is `Γ ⊢ ?g : φ`. Transform it into `Γ ⊢ ¬φ -> True -> False`,
  -- as that is the proof type that cvc5 spits out (`unsat`).
  let g <- getMainGoal
  let φ : Q(Prop) <- g.getType
  let [g'] <- g.apply q(@smt_harness $φ)
    | throwError "Applying smt_harness resulted in zero or more than one goals."
  replaceMainGoal [g']
  withMainContext do
    liftATacticM do
      elabACommands aproof
      withMainContext do
        evalTactic (<- `(tactic| assumption)) -- last step is (it better be..) `False`, use that.
  let proof <- instantiateMVars (Expr.mvar g)
  loggInfo m!"Proof term is {proof}"

elab c:acmd : tactic => liftATacticM do elabACommand c

elab "smtProof " prf:aproof : tactic => do
  let `(aproof| unsat $cmds*) := prf | throwError "unexpected syntax"
  smtHarness cmds

theorem test_individual_alethe_commands : True ∨ False := by
  apply Classical.byContradiction
  -- have truth : True := .intro
  -- revert truth
  (assume a0 (not (or true false)))
  -- (assume a1 true)
  (step t1 (cl (not (= (not (or true false)) false)) (not (not (or true false))) false) :rule equiv_pos2)
  (step t2 (cl (= (or true false) true)) :rule all_simplify)
  (step t3 (cl (= (not (or true false)) (not true))) :rule cong :premises (t2))
  (step t4 (cl (= (not true) false)) :rule all_simplify)
  (step t5 (cl (= (not (or true false)) false)) :rule trans :premises (t3 t4))
  (step t6 (cl) :rule resolution :premises (t1 t5 a0))
  exact t6

#print axioms test_individual_alethe_commands

theorem test_alethe_proof : True ∨ False := by
  smtProof
    unsat
    (assume a0 (not (or true false)))
    (assume a1 true)
    (step t1 (cl (not (= (not (or true false)) false)) (not (not (or true false))) false) :rule equiv_pos2)
    (step t2 (cl (= (or true false) true)) :rule all_simplify)
    (step t3 (cl (= (not (or true false)) (not true))) :rule cong :premises (t2))
    (step t4 (cl (= (not true) false)) :rule all_simplify)
    (step t5 (cl (= (not (or true false)) false)) :rule trans :premises (t3 t4))
    (step t6 (cl) :rule resolution :premises (t1 t5 a0))

#print axioms test_alethe_proof

