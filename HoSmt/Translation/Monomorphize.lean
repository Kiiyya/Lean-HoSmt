import HoSmt.Util
import Lean

import Lean
import Lean.Data
import HoSmt.Translation.TransM
import HoSmt.Translation.OccurenceRewriting
import HoSmt.Translation.Patterns
import HoSmt.Util

open Lean Elab Term Command Tactic Expr Std
open HoSmt.Translation.TransM HoSmt.Util TermElabM HoSmt.Translation.Patterns

namespace HoSmt.Translation.Monomorphize

initialize registerTraceClass `HoSmt.Translation.Mono
initialize registerTraceClass `HoSmt.Translation.Mono.traverse
initialize registerTraceClass `HoSmt.Translation.Mono.traverseConst
initialize registerTraceClass `HoSmt.Translation.Mono.patterns
initialize registerTraceClass `HoSmt.Translation.Mono.ind
initialize registerTraceClass `HoSmt.Translation.Mono.indArgs
initialize registerTraceClass `HoSmt.Translation.Mono.def
initialize registerTraceClass `HoSmt.Translation.Mono.defArgs

def primitives : List Name := [``Eq, ``Nat.add, ``Subtype, ``sorryAx]
def skipBodies : List Name := [``ite]

private def checkArgPatMatch (arg : Option Expr) (pat : Option Expr) : TransM Bool := do
  match arg, pat with
  | some arg, some pat => return (<- Meta.withReducible <| Meta.whnf arg) == (<- Meta.withReducible <| Meta.whnf pat) -- Meta.isDefEq arg pat
  | some _, none => return false
  | none, some _ => return false
  | none, none => return true

/--
  Given a type `ty` such as `(n : Nat) -> (α : Type) -> (l : List α) -> body`,
  this function will return `[false, true, false]`, meaning that the second param needs to be
  mono'd.
-/
partial def determineMonoPatternDef (ty : Expr) : MetaM (Array Bool) := do
  let (pat, _) <- go2 ty false
  return pat.toArray
where
  go2 (expr : Expr) (monoInSubtree : Bool) : MetaM <| List Bool × HashSet FVarId := do
    let (a, b) <- go expr monoInSubtree
    if (<- Meta.inferType expr).isProp then
      return (a, {})
    else
      return (a, b)

  go (expr : Expr) (monoInSubtree : Bool) : MetaM <| List Bool × HashSet FVarId := do
    let rec log
    | .ok (pat, constrFVars) => do
      let set <- constrFVars.toArray.mapM (fun fv => fv.getUserName)
      return m!"determineMonoPatternDef.go[monoInSubtree={monoInSubtree}] {expr} ~~> ({pat}, {set})"
    | _ => return m!"determineMonoPatternDef.go[monoInSubtree={monoInSubtree}] {expr} ~~> error"

    withTraceNode `HoSmt.Translation.Mono.patterns log do
      -- whnf will turn `outParam Type` into `Type`
      let expr <- Meta.withReducible <| Meta.whnf expr
      match expr with
      | .forallE _ dom _ _ => do
        let dom <- Meta.withReducible <| Meta.whnf dom
        let (_, constrainedFVarsDom) <- go2 dom monoInSubtree
        -- logInfo "[go1] dom is {repr dom}"
        Meta.forallBoundedTelescope expr (some 1) fun fvars body => do 
          let fvar := fvars[0]!
          let (patternBody, constrainedFVarsBody) <- go2 body monoInSubtree
          -- This parameter needs to be monomorphized if..
          let needMono :=
            dom.isType -- it's a `(α : Type _) -> ...` binder
            || constrainedFVarsBody.contains fvar.fvarId! -- it occurs as a type parameter `(x : α) -> ... T x`
          return (
            needMono :: patternBody,
            constrainedFVarsDom
              |>.insertMany constrainedFVarsBody
              |>.erase fvar.fvarId!
          )
      | .lam _ dom _ _ => do
        let dom <- Meta.withReducible <| Meta.whnf dom
        let (_, c_dom) <- go2 dom monoInSubtree
        Util.withLambda expr fun _fv body => do
          let (_, c_body) <- go2 body monoInSubtree
          return ([], c_dom.insertMany c_body)
      | .app _ _ => do
        -- TODO: what about `(x : someClass.numType) -> ...` ?
        
        -- Given `expr === f args`, check whether `f : ... -> Type _`.
        -- This is the case for inductive types (`List : Type -> Type`), and... maybe for some more things, but mainly inductive types.
        let isDotDotDotType <- Meta.forallBoundedTelescope (<- Meta.inferType expr.getAppFn) none fun _ body => do
          return body.isType

        let (_, goF) <- go2 expr.getAppFn monoInSubtree -- not sure, might need `|| isDotDotDotType`?

        -- descend into args, any any fvars occuring inside this will be marked as constrained.
        let args := expr.getAppArgs
        let constrainedFVars <- args.foldlM
          (fun acc arg => do return acc.insertMany (<- go2 arg (isDotDotDotType || monoInSubtree)).2)
          goF
        return ([], constrainedFVars) -- once we're no longer in the root forallTelescope, pattern is meaningless.
      | .const _ _ => do return ([], {})
      | .fvar id => do
        if monoInSubtree then
          return ([], HashSet.empty.insert id)
        else
          return ([], {})
      | .sort .zero => return ([], {})
      | .sort level =>
        return ([], {})
      | .lit _ => return ([], {})
      | .proj _ idx obj => do
        -- TODO descend into obj AND into projection function!
        go2 obj monoInSubtree
      | _ => throwError "determineMonoPatternDef: going into {expr} not supported."

#eval determineMonoPatternDef <|
  mkForall `alpha .default (.sort (.succ .zero)) <|
    (Expr.const ``Nat [])

#check @id
set_option pp.all true in
#eval determineMonoPatternDef <|
  mkForall `alpha .default (.sort (.param `u)) <|
    (Expr.const ``Nat [])

private def checkViableMonoArg : (arg : Option Expr) -> TransM Bool
| none => return true -- trivially
| some arg => do
  if <- isSimpleType arg then return true
  -- TODO: If we have `List (List Nat)`, which is monomorphizable, we needlessly reject it :(.
  if arg.hasAnyFVar (fun _ => true) then return false
  return true -- yolo :)

private def determineMonoPatternInd (ty : Expr) : TransM (Array Bool) := do
  determineMonoPatternDef ty

initialize registerTraceClass `HoSmt.Translation.Mono.cache

private def debugHelper (mm: HashMap (Array (Option Expr)) MonomorphizedInfo) : TransM MessageData := do
  let inner <- mm.toArray.foldlM (fun acc (pat, _) => do return m!"{acc}, {pat} ↦ (monoinfo here)") m!""
  return m!"\{{inner}}"

/--
  Check whether the item has already been monomorphized for the given args pattern.

  Not feeling too sure about this implementation, especially the `Meta.isDefEq` part.
-/
private def checkMonoMapArgs (item : Name) (args : Array (Option Expr)) : TransM (Option MonomorphizedInfo) := do
  trace[HoSmt.Translation.Mono.cache] "checkMonoMapArgs (1) {item} {args}"
  let some mm := (<- get).monoMapArgs.find? item | return none
  trace[HoSmt.Translation.Mono.cache] "checkMonoMapArgs (2) mm = {<- debugHelper mm}"
  Term.synthesizeSyntheticMVarsUsingDefault
  for (pattern, monoInfo) in mm.toArray do
    let overlapLen := Nat.min args.size pattern.size
    trace[HoSmt.Translation.Mono.cache] "checkMonoMapArgs (3) pattern = {pattern}, overlapLen = {overlapLen}"
    if pattern[overlapLen:].any (fun x => x.isSome) then continue
    if args[overlapLen:].any (fun x => x.isSome) then continue
    
    -- Determine whether all args are DefEq
    let x <- Array.zip args pattern |>.allM fun (arg, pat) => checkArgPatMatch arg pat
    trace[HoSmt.Translation.Mono.cache] "checkMonoMapArgs (4) x = {x}"
    if x then return monoInfo
  return none

/--
  Check whether the item has already been monomorphized.
-/
private def checkMonoMapGeneral (item : Name) : TransM (Option MonoTraversal) := do
  return (<- get).monoMapGeneral.find? item

initialize registerTraceClass `HoSmt.Translation.Mono.applyLambdasPattern
initialize registerTraceClass `HoSmt.Translation.Mono.applyForallsPattern

/--
  Given a type `(x₁ : τ1) -> ... -> (x_n : τ_n) -> body`, (for example `List : (x₁ : Type) -> Type`),
  and a pattern to monomorphize `#[a₁, a₂, ...]` (for example `#[some Nat]`),
  and produce the monomorphized type by substituting `x_i` with `a_i` if `a_i` isSome (for example `List : Type`).
  ```
  ty   === (x₁ : τ₁) -> (x₂ : τ₂ x₁) -> (x₃ : τ₃ x₁ x₂) -> body x₁ x₂ x₃
  args === [none,       some y,         none]
  ```
  becomes
  ```
           (x₁ : τ₁) ->                 (x₃ : τ₃ x₁ y) -> body x₁ y x₃
  ```
-/
private def applyForallsPattern (ty : Expr) (args : List <| Option Expr) : MetaM Expr := do
  let log
  | .ok res => return m!"{ty} with args {args} ~~> {res}"
  | _ => return m!"{ty} with args {args} ~~> error"
  withTraceNode `HoSmt.Translation.Mono.applyForallsPattern log do
    if args.all (fun x => x.isNone) then return ty -- no more args to apply.
    match args with
    | [] => return ty -- no more args to apply
    | arg :: tail =>
      if !ty.isForall then
        throwError "Still got concrete args to apply, but ran out of foralls? ty === {ty}, args === {args}"
      Meta.forallBoundedTelescope ty (some 1) fun fvs body => do
        match arg with
        | none =>
          -- `(x:τ) -> body` becomes `(x:τ) -> body'`
          Meta.mkForallFVars fvs (<- applyForallsPattern body tail)
        | some arg =>
          -- `(x:τ) -> body` becomes `body[x ↦ arg]`
          -- if let .const name lvls := arg then
            -- let lvls <- lvls.mapM (fun _ => do return Level.mvar (<- mkFreshLMVarId))
            let body' := body.replaceFVar fvs[0]! arg
            applyForallsPattern body' tail
          -- else throwError "applyForallsPattern: currently only `Expr.const` args are supported, but got {arg} (which has repr {repr arg})"

section test
  -- List Nat
  #eval applyForallsPattern
    (.forallE `α (Expr.sort <| .succ .zero) (mkApp (mkConst ``List) (.bvar 0)) .default)
    [some (mkConst ``Nat)]

  -- {α β : Type} → α → Either α β ~~> Nat → Either Nat Nat
  #eval applyForallsPattern (
    mkForall `α .default (.sort <| .succ .zero) <|
      mkForall `β .default (.sort <| .succ .zero) <|
        mkForall `val .default (.bvar 1) <|
          mkConst ``Or
  )
  [some (mkConst ``Nat), some (mkConst ``Nat)]

  inductive τ₁ : Type
  inductive τ₂ : Type
  inductive τ₃ : Type
  #eval do return s!"{<- applyForallsPattern (
      mkForall `x₁ .default (mkConst ``τ₁) <|
        mkForall `x₂ .default (mkApp (mkConst ``τ₂) (.bvar 0)) <|
          mkForall `x₃ .default (mkApp2 (mkConst ``τ₃) (.bvar 1) (.bvar 0)) <|
            mkApp3 (mkConst `body) (.bvar 2) (.bvar 1) (.bvar 0)
    )
    [none, some (mkConst `y), none]}"
end test

/--
  Like applyForallsPattern, but for lambda binders instead.
-/
private def applyLambdasPattern (lams : Expr) (args : List <| Option Expr) : MetaM Expr := do
  let log
  | .ok res => return m!"{lams} ~~> {res}"
  | _ => return m!"{lams} ~~> error"
  withTraceNode `HoSmt.Translation.Mono.applyLambdasPattern log do
    if args.all (fun x => x.isNone) then return lams -- no more args to apply.
    match args with
    | [] => return lams -- no more args to apply
    | arg :: tail =>
      if !lams.isLambda && !lams.isSorry then
        throwError "Still got concrete args to apply, but ran out of foralls? lams === {lams}, args === {args}"
      withLambda lams fun fv body => do
        match arg with
        | none => Meta.mkLambdaFVars #[.fvar fv] (<- applyLambdasPattern body tail)
        | some arg => do
          -- if let .const name lvls := arg then
            -- let lvls <- lvls.mapM (fun _ => do return Level.mvar (<- mkFreshLMVarId))
            let body' := body.replaceFVarId fv arg
            -- let body' <- instantiateMVars body'
            applyLambdasPattern body' tail
          -- else throwError "applyLambdasPattern: currently only `Expr.const` args are supported, but got {arg} (which has repr {repr arg})"

/-- Trims extra `none`s from the end. -/
def trimPattern (pattern : Array (Option α)) : Array (Option α) :=
  go pattern.toList |>.toArray
where
  go : List (Option α) -> List (Option α)
  | [] => []
  | list@(x :: xs) => if list.all Option.isNone then [] else x :: (go xs)

/--
  Returns the monomorphized variant of inductive type T to args_exprs (for example to `#[Nat]` for T=List).

  `levels` should be the levels in `(.const T levels)`.

  Currently this function assumes that we supply *all* args, i.e. that `args.length = arity of T` and that all are `some`.
-/
private def monoOfInductive (T : InductiveVal) (levels : List Level) (args : Array (Option Expr)) : TransM (Option MonomorphizedInfo) := do
  if args.all Option.isNone then
    return none
  if primitives.contains T.name then
    return none

  if args.size < T.numParams + T.numIndices then
    -- this if is not quite accurate since we can handle arg patterns...
    throwError "Can't monomorphize {Expr.const T.name levels} for {args}, expected {T.numParams} + {T.numIndices} arguments but only found {args.size}"

  unless <- args.allM checkViableMonoArg do
    throwError "Monomorphizing {Expr.const T.name levels} for {args} not possible: not all args are viable."

  if let some mono := <- checkMonoMapArgs T.name args then
    trace[HoSmt.Translation.Mono.cache] "monoOfInductive: Mono cache hit for {T.name}"
    return mono

  let monoSuffix <- mkFreshId
  let M := T.name ++ monoSuffix
  let log
  | .ok res => pure m!"Monomorphizing inductive type {Expr.const T.name levels} for args {trimPattern args} ~~> {res}"
  | .error e => pure m!"Monomorphizing inductive type {Expr.const T.name levels} for args {args} ~~> error, {e.toMessageData}"
  withTraceNode `HoSmt.Translation.Mono.indArgs log do
    assert! T.levelParams.length == levels.length
    let TType := instantiateLevelParams T.type T.levelParams levels
    let MType <- applyForallsPattern TType args.toList
    let MnumParams := args[:T.numParams].toArray.filter Option.isNone |>.size -- the amount of params left. (tho if we mono a Guard from index erasure, maybe some params get demoted to indices? :/)
    trace[HoSmt.Translation.Mono.indArgs] "resulting MType is {MType}, and has numParams = {MnumParams}"
    let MLevelParams := Lean.collectLevelParams {} MType |>.params |>.toList -- assuming all level params must occur in the resulting inductive type's type, this should be sufficient.

    -- change ctors
    -- from `List.cons     :  {α:Type} -> α   -> List α   -> List α  `
    -- into `List.cons_Nat :              Nat -> List Nat -> List Nat` (note: not `List_Nat` yet!)
    Meta.withLocalDeclD M MType fun Mfvar => do
      let mut ctors := []
      let mut ctorNameMap : HashMap Name Name := {}
      for ctorName in T.ctors do
        trace[HoSmt.Translation.Mono.indArgs] "handling ctor {ctorName}"
        let ctor <- getCtor! ctorName
        let ctorType := instantiateLevelParams ctor.type T.levelParams levels
        -- Each ctor has a prefix of binders corresponding to the type params of its inductive type.
        -- Turn `{α:Type} -> α -> List α -> List α` into `Nat -> List Nat -> List Nat`
        let ctor' <- applyForallsPattern ctorType args.toList 

        -- Each ctor still contains occurences `List Nat`, so turn them into `List_Nat`.
        let rewriter : Expr -> TransM Expr := fun e => do
          if !e.isAppOf T.name then return e
          -- Since we can not have type indices once we get to the monomorphization stage,
          -- we know that any occurences of `T` *must* have exactly the args we mono to.
          -- So we can skip the following check:
          -- let hasOurArgPattern <- Array.zip args e.getAppArgs |>.allM fun (arg, pat) => checkArgPatMatch arg pat
          -- if e.getAppArgs != args then return e
          let pattern := args.map (fun arg => arg.isSome) |>.toList
          let e' := mkAppN Mfvar (<- filterByPatternInv e.getAppArgs.toList pattern).toArray
          -- let e' <- Meta.mkAppOptM' Mfvar ((<- filterByPatternInv e.getAppArgs.toList pattern).toArray.map (fun x => some x))
          trace[HoSmt.Translation.Mono.indArgs] "rewriting {e} to {e'}"
          return e'
        let ctor'' := (<- OccurenceRewriting.descendingRewriter rewriter ctor' "(ctor'')").replaceFVar
          Mfvar
          (Lean.mkConst M (MLevelParams.map Level.param))

        let ctor'Name := ctor.name ++ monoSuffix -- List.ctor_Nat
        trace[HoSmt.Translation.Mono.indArgs] "{ctor'Name} : {ctor''}"
        ctorNameMap := ctorNameMap.insert ctorName ctor'Name
        ctors       := ctors ++ [Constructor.mk ctor'Name ctor'']

      let addDeclResult <- addInductiveDecl MLevelParams MnumParams M T.name MType ctors false

      -- register our translated items in the mono cache.
      let monoInfo := MonomorphizedInfo.induct M ctorNameMap
      registerMonoOfArgs T.name args monoInfo
      if let some projFnsMapping := addDeclResult.projFnsMapping then
        -- if we monomorphized a structure, `addInductiveDecl` also derived new projection functions.
        projFnsMapping.forM fun old new => registerMonoOfArgs old args <| .defn new
      return monoInfo


/--
  If we encounter a function typed `List.length {α:Type} : List α -> Nat` in an occurence such as
  `List.length (α := String) ["thing"]`, we can use this function to "partially apply" the function
  to the arguments.

  The result of this will be `List.length' : List String -> Nat`, i.e. **still containing a reference
  to polymorphic type `List`!**
  You need to call `monoOfDef` again to also mono all occurences of polymorphic types.

  This function does *not* determine which parameters need to be monomorphized.
  Instead, it takes an array of args to monomorphize to. For example, `#[none, some (42)]`
  will monomorphize the second parameter to value 42, but leaving the first one in tact.
  So a function `f a₁ a₂ a₃` will become `f' a₁ a₃`.
-/
private partial def monoOfDefArgs (name : Name) (levels : List Level) (args : Array (Option Expr)) : TransM Name := do
  let some defn := (<- getEnv).find? name | throwError "No such env item {name}"
  match defn with
  | .thmInfo .. | .defnInfo .. | .axiomInfo .. => pure
  | _ => throwError "monoOfDefArgs can only be invoked on a definition, theorem, or axiom."

  if args.all (fun a => a.isNone) then return name
  unless <- args.allM checkViableMonoArg do
    throwError "Monomorphizing {defn.name} for {args} not possible: not all args are viable."
  if let some mono := <- checkMonoMapArgs defn.name args then
    trace[HoSmt.Translation.Mono.cache] "monoOfDefArgs: cache hit for {defn.name}"
    return mono.defn!
    
  let log
  | .ok n' => return m!"Monomorphizing defn {Expr.const defn.name levels} for args {trimPattern args} ~~> {n'}"
  | .error err => return m!"monoOfDefArgs {Expr.const defn.name levels} for args {args} ~~> error: {err.toMessageData}"
  withTraceNode `HoSmt.Translation.Mono.defArgs log do
    ensureHasEqns defn.name -- Equations for the *original* defn. We will monomorphize these as well.

    let monoSuffix <- mkFreshId
    let name' := defn.name ++ monoSuffix

    -- Partially reduce our `defn`. This is where the mono happens.
    -- `f   : (α : Type) -> (l : List α  ) -> Ret` becomes
    -- `f_1 :               (l : List Nat) -> Ret`
    let (defn', _) <- ConstantInfo.modify defn name'
      (fun type => applyForallsPattern (instantiateLevelParams type defn.levelParams levels) args.toList)
      (fun value => do
        -- if value.getUsedConstants.contains ``sorryAx then
        --   Meta.mkSorry 
        applyLambdasPattern (instantiateLevelParams value defn.levelParams levels) args.toList
      )

    let mut defn' := defn'
    if skipBodies.contains defn.name then
      trace[HoSmt.Translation.sry] "monoOfDefArgs[{name}] This const is in skipBodies. Replacing body with sorryAx."
      defn' := <- ConstantInfo.removeBody defn'  
    
    trace[HoSmt.Translation.Mono.defArgs] "addDecl {ciKind defn'} {name'}.{defn'.levelParams}\n:::{defn'.type}\n==={defn'.value?}"
    addDecl <| <- ConstantInfo.toDefnLikeDecl defn'

    modify fun s =>
      let updatedVariants := s.monoMapArgs.findD defn.name {} |>.insert args (MonomorphizedInfo.defn name')
      { s with monoMapArgs := s.monoMapArgs.insert defn.name updatedVariants }

    -- Preserve equations (also monomorphize them.)
    let eqns' <- (<- get).equations.find? defn.name |>.mapM (fun x => x.toArray.mapM (monoOfDefArgs . levels args))
    registerEquations name' eqns'

    return name'

/--
  Go through the type and value of this definition and replace occurences of polymorphic types
  `T args` with its monomorphized variant `T_mono123`.

  This function **assumes no `(α:Type) -> ...` binders in the defn type!**.
  In order to get rid of `(α:Type) ->..` binders, you need to call `monoOfDefArgs` first and pass
  in a concrete type.

  So from...
  ```
    @map : (f : α -> β) -> List α -> List β
      := λf, λl, body
  ```
  construct, using `sorry` since there are recursors,...
  ```
    @map' : (f : α -> β) -> List₁ -> List₂
      := sorry
  ```
-/
private partial def traverseConst' (name : Name) (traverse : Expr -> Option Name -> TransM Expr) : TransM Name := do
  match <- checkMonoMapGeneral name with
  | some .notNecessary =>
    trace[HoSmt.Translation.Mono.cache] "traverseConst': Mono cache hit for {name}"
    return name
  | some (.mono name') =>
    trace[HoSmt.Translation.Mono.cache] "traverseConst': Mono cache hit for {name}"
    return name'
  | none => pure ()
  trace[HoSmt.Translation.Mono.cache] "traverseConst': Mono cache miss for {name}, checking whether mono necessary.."

  let some ci := (<- getEnv).find? name
    | throwError "no such const {name}"

  let log
  | .ok ret => return m!"{name} ~~> {repr ret}"
  | _ => do
    let some ci := (<- getEnv).find? name | throwError "(!!! log) no such const {name}"
    return m!"traverseConst' {Expr.const name (ci.levelParams.map Level.param)} (levelParams from decl = {ci.levelParams}) ~~> error"
  withTraceNode `HoSmt.Translation.Mono.traverseConst log do
    let ret <- go ci
    -- `ret` is now either the old name (if traversal ended up not changing anything),
    -- or the new updated constant. Either way, traverse the equations now.
    let equations := (<- get).equations.findD ret {} |>.toArray
    let equations' <-
      if !equations.isEmpty then
        withTraceNode `HoSmt.Translation.Mono.traverseConst (fun res => do return  m!"traverseConst({name} ↦ {ret}) {ret} has equations: {equations} ~~> {if let .ok res := res then m!"{res}" else "error"}")
          (equations.mapM (traverseConst' . traverse))
      else pure #[]
    replaceEquations ret equations equations'

    return ret
where
  go ci : TransM Name := do
    let uniq <- mkFreshId
    let name' := name ++ uniq
    -- let type := replaceConst name name' ci.type
    let type' <- withTraceNode `HoSmt.Translation.Mono.traverse (fun _ => pure m!"Traversing type of {ciKind ci} {name}..") do
      traverse ci.type name
    match ci with
    | .thmInfo thm => do
      let mut result : MonoTraversal := .notNecessary -- returning same name ==> no mono happened
      if ci.type != type' then
        withTraceNode `HoSmt.Translation.Mono (fun _ => pure m!"Monomorphizing thm {name} ~~> addDecl theorem {name'}\n:::{type'}") do
          addDecl <| Declaration.thmDecl { thm with
            name := name',
            all := [name'],
            -- TODO: levelParams := sorry,
            type := type',
            value := <- Meta.mkSorry type' true, -- don't bother translating proofs
          }
          trace[HoSmt.Translation.Mono] "success (addDecl {name'})"
        result := .mono name'
      modify fun s => { s with monoMapGeneral := s.monoMapGeneral.insert name result }
      return result.getD name
    | .defnInfo defn => do
      ensureHasEqns defn.name
      -- let defnType := defn.type.instantiateLevelParams 
      
      let value' <- withTraceNode `HoSmt.Translation.Mono.traverse (fun _ => pure m!"Traversing value of {name}..") do
        if skipBodies.contains name then
          trace[HoSmt.Translation.sry] "traverseConst'[{name}] Replacing body with sorryAx."
          Meta.mkSorry type' true
        else
          traverse defn.value name

      -- if type or value changed, add a new decl.
      let mut result : MonoTraversal := .notNecessary
      if type' != ci.type || value' != defn.value then
        withTraceNode `HoSmt.Translation.Mono (fun _ => pure m!"Monomorphizing defn {name} ~~> addDecl def {name'}\n:::{type'}\n==={value'}") do
          addDecl <| Declaration.defnDecl { defn with
            name := name',
            all := [name'],
            -- TODO: levelParams := sorry,
            type := type', -- a function f can not appear in its own type, hence no need for replaceConst.
            value := replaceConst name name' value', -- replace recursive usages (not sure if this is the right way?)
          }
          trace[HoSmt.Translation.Mono] "success (addDecl {name'})"
        result := .mono name'
        registerEquations name' <| (<- get).equations.find? name -- these will be traversed at the end of traverseConst'
      modify fun s => { s with monoMapGeneral := s.monoMapGeneral.insert name result }
      return result.getD name
    | .axiomInfo defn => do
      -- if type or value changed, add a new decl.
      let mut result : MonoTraversal := .notNecessary
      if type' != ci.type then
        withTraceNode `HoSmt.Translation.Mono (fun _ => pure m!"Monomorphizing axiom ~~> addDecl axiom {name'}\n:::{type'}") do
          addDecl <| Declaration.axiomDecl { defn with
            name := name',
            -- TODO: levelParams := sorry,
            type := type', -- a function f can not appear in its own type, hence no need for replaceConst.
          }
          trace[HoSmt.Translation.Mono] "success (addDecl {name'})"
        result := .mono name'
      modify fun s => { s with monoMapGeneral := s.monoMapGeneral.insert name result }
      return result.getD name

    | .inductInfo T => do
      let ctors' : List (Constructor × Bool × /- old name -/ Name) <- T.ctors.mapM fun ctorName => do
        let ctor <- TermElabM.getCtor! ctorName
        let type' <- withTraceNode `HoSmt.Translation.Mono.traverse (fun _ => pure m!"Traversing ctor {ctorName}...") do
          traverse ctor.type name
        let decl : Constructor := {
          name := ctorName ++ uniq,
          type := replaceConst name name' type'
        }
        return (decl, type' != ctor.type, ctorName)
      
      let anyChange := ctors'.any (fun (_, b, _) => b) || type' != ci.type
      if anyChange then
        withTraceNode `HoSmt.Translation.Mono (fun _ => pure m!"Monomorphizing {name} ~~> addInductiveDecl {name'}\n:::{type'}\nctors...") do
          let addDeclResult <- addInductiveDecl T.levelParams T.numParams name' name type' (ctors'.map Prod.fst) T.isUnsafe
          trace[HoSmt.Translation.Mono] "success (addInductiveDecl {name'})"
          if let some projFnsMapping := addDeclResult.projFnsMapping then
            -- if we monomorphized a structure, `addInductiveDecl` also derived new projection functions.
            -- Too lazy to add the "not necessary" marker on the projection functions if !anyChange, but
            -- if T didn't need changes, then the projection functions won't either, I hope.
            projFnsMapping.forM fun old new => registerMonoGeneral old <| MonoTraversal.mono new

      -- Add `T ↦ T'` as well as all ctors `T.c ↦ T'.c` to the general mono cache for faster lookup:
      modify fun s =>
        let map := s.monoMapGeneral.insert name (if anyChange then .mono name' else .notNecessary)
        let map := ctors'.foldl
          (fun map (newCtor, _, oldCtor) => map.insert oldCtor (if anyChange then .mono newCtor.name else .notNecessary))
          map
        { s with monoMapGeneral := map }
      return if anyChange then name' else name
    | .ctorInfo C => do
      -- No mono cache entry for this ctor exists, which means that no mono cache entry for its
      -- corresponding inductive type T exists either.
      -- Then after traversing T there *must* be an entry for C, so just return that.
      -- We don't need to consider mono patterns, since if T was mono'd via monoOfInductive, that is handled
      -- inside traverse' specially (the .app match arm, not the .const match arm).
      withTraceNode `HoSmt.Translation.Mono.traverse (fun _ => pure m!"traverseConst' ctor {C.name}: First traverseConst' its corresponding inductive type {C.induct}...") do
        let _ <- traverseConst' C.induct traverse
      let some info <- checkMonoMapGeneral C.name
        | throwError "while traverseConst' {C.name}: Traversing {C.induct} did not populate monoCacheGeneral for {C.name}."
      return info.getD name
    | .recInfo R => do
      trace[HoSmt.Translation.Mono] "traverseConst': Ignoring recursor {R.name} : {R.type}"
      return name
    | _ => throwError "Monomorphize.traverseConst' not yet impl for consts such as {name} (which is a {Util.ciKind ci})"

/-- `doNotDescend` is used to exempt the currently-traversed const from descending a second time
  and causing an infinite loop. Bit of a hacky solution, but it's quick and works for now. -/
private partial def traverse' (e : Expr) (doNotDescend : Option Name) : TransM Expr := do
  let e := e.consumeTypeAnnotations
  antiStackOverflow do
    let descend (e : Expr) : TransM Expr := traverse' e doNotDescend
    let log : Except Exception Expr -> TransM MessageData
    | .ok expr => return m!"traversing[{e.ctorName}](dnd={doNotDescend}) {e} ~~> {expr}"
    | _ => return m!"traversing[{e.ctorName}](dnd={doNotDescend}) {e} ~~> error"

    if e.isSorry then
      let args := e.getAppArgs
      let ty := args[0]!
      trace[HoSmt.Translation.Mono.traverse] "Encountered a sorry, translating its expected type as well..."
      let ty' <- traverse' ty doNotDescend
      return <- Meta.mkSorry ty' true

    withTraceNode `HoSmt.Translation.Mono.traverse log do
      let e <- instantiateMVars e
      match e with
      | .app appF appA => do
        let fn := e.getAppFn
        trace[HoSmt.Translation.Mono.traverse] ".app (1) fn = {fn}"
        if let some (name, levels) := fn.const? then
          if primitives.contains name then
            return .app (<- descend appF) (<- descend appA)
          let some ci := (<- getEnv).find? name | throwError "No such constant {name}"
          trace[HoSmt.Translation.Mono.traverse] ".app (2) ci = {ci.name} [{ciKind ci}] ..."
          let args := e.getAppArgs
          trace[HoSmt.Translation.Mono.traverse] ".app (3) args = {args}"
          
          match ci with
          | .inductInfo T => do
            -- Replace `T args` with `T_args`
            let Ttype := T.type.instantiateLevelParams ci.levelParams levels
            let pattern := (<- determineMonoPatternInd Ttype).toList
            trace[HoSmt.Translation.Mono.traverse] ".app (4) pattern = {pattern}"
            if let some mono := <- monoOfInductive T levels (<- stencilPattern args.toList pattern).toArray then
              let .induct name _ctors := mono | throwError "{T.name} is not induct mono info?"
              trace[HoSmt.Translation.Mono.traverse] ".app (5) some mono = .induct {name}"
              let leftovers <- filterByPatternInv args.toList pattern
              let indInfo <- getConstInfoInduct name
              trace[HoSmt.Translation.Mono.traverse] ".app (6) leftovers = {leftovers}"
              return <- descend <| mkAppN (.const name (indInfo.levelParams.map Level.param)) leftovers.toArray
          | .ctorInfo info => do
            -- Replace `ctor U rest` with `ctor_U rest`
            let T <- getInduct! info.induct
            let Ttype := T.type.instantiateLevelParams ci.levelParams levels -- ctors have the same levelParams as their inductive type
            let pattern := (<- determineMonoPatternInd Ttype).toList
            trace[HoSmt.Translation.Mono.traverse] ".app (4) pattern = {pattern}"
            if let some mono := <- monoOfInductive T levels (<- stencilPattern args[:T.numParams].toArray.toList pattern).toArray then
              -- let pattern := List.repeat [true] T.numParams -- TODO: handle extra ctor polymorphism.
              let .induct T' monoCtors := mono | throwError "{T.name} is not induct mono info?"
              trace[HoSmt.Translation.Mono.traverse] ".app (5) some mono = .induct {T'} {monoCtors}"
              let some ctorMono := monoCtors.find? name
                | throwError "While monomorphizing type {T.name}, poly ctor {name} doesn't have mono variant in monoInfo?"
              let T'ci <- getConstInfoInduct T'
              let levels' := T'ci.levelParams.map Level.param
              let e' := mkAppN (.const ctorMono levels') (<- filterByPatternInv args.toList pattern).toArray
              -- let e' <- Meta.mkAppOptM ctorMono ((<- filterByPatternInv args.toList pattern).toArray.map (fun x => some x))
              trace[HoSmt.Translation.Mono.traverse] ".app (6) e' = {e'}"
              return <- descend e'
          | .defnInfo F => do
            -- special handling for OfNat (very hacky).
            if F.name == ``OfNat.ofNat then
              if e.getAppArgs[0]? == some (.const ``Nat []) then
                if let some nat := e.getAppArgs[1]? then
                  return <- descend nat

            let Ftype := F.type.instantiateLevelParams F.levelParams levels
            -- let Fval := F.value.instantiateLevelParams F.levelParams levels
            let pattern : List Bool := (<- determineMonoPatternDef Ftype).toList
            trace[HoSmt.Translation.Mono.traverse] ".app (4) pattern = {pattern}"
            let F' <- monoOfDefArgs F.name levels (<- stencilPattern args.toList pattern).toArray
            if F.name != F' then
              trace[HoSmt.Translation.Mono.traverse] ".app (5)"
              let leftovers := (<- filterByPatternInv args.toList pattern).toArray
              let monoDefnInfo <- getConstInfoDefn F'
              -- Note that we only mono `List.length` in the following example, and the rest
              -- gets mono'd when we descend subsequently.
              -- e = `List.length String (.cons String "Hi" (.nil String))`
              -- becomes
              -- e' = `List.length' (.cons String "Hi" (.nil String))`
              let e' := mkAppN (.const F' (monoDefnInfo.levelParams.map Level.param)) leftovers
              -- The following will not result in endless recursion, since 
              return <- descend e'
          | .axiomInfo F => do
            let Ftype := F.type.instantiateLevelParams F.levelParams levels
            let pattern : List Bool := (<- determineMonoPatternDef Ftype).toList
            trace[HoSmt.Translation.Mono.traverse] ".app (4) pattern = {pattern}"
            let F' <- monoOfDefArgs F.name levels (<- stencilPattern args.toList pattern).toArray
            if F.name != F' then
              trace[HoSmt.Translation.Mono.traverse] ".app (5)"
              let leftovers := (<- filterByPatternInv args.toList pattern).toArray
              let monoDefnInfo <- getConstInfo F'
              let e' := mkAppN (.const F' (monoDefnInfo.levelParams.map Level.param)) leftovers
              -- The following will not result in endless recursion, since 
              return <- descend e'
          | _ => throwError "Mono traverse' encountered app with fn = {fn}, which is CI kind {ciKind ci}. Don't know how to translate."
        return .app (<- descend appF) (<- descend appA)
      | .const name levels => do
        if doNotDescend == some name || primitives.contains name then
          return e
        trace[HoSmt.Translation.Mono.traverse] "traversing {repr e}"

        let name' <- traverseConst' name traverse'
        if name != name' then
          let ci <- getConstInfo name'
          return .const name' (ci.levelParams.map Level.param)
        return e
      | .fvar .. => return e
      | .lit .. => return e
      | .sort .. => return e
      | .mdata md inner => return .mdata md (<- descend inner)
      | .proj T idx obj => do
        trace[HoSmt.Translation.Mono.traverse] "this is a projection T={T}, idx={idx}"
        -- special handling for `(instOfNatNat n).ofNat` ~~> `n`
        if T == ``OfNat then
          let objType <- Meta.inferType obj
          if objType.getAppArgs[0]? == some (.const ``Nat []) then
            if obj.isAppOf ``instOfNatNat then
              if let some nat := obj.getAppArgs[0]? then
                return <- descend nat

        -- if `obj` is an fvar, this will do nothing.
        -- if `obj` is a const or a `(T.mk ...)`, this will traverse it accordingly.
        let obj' <- descend obj
        -- Assumption: Given `T : ... -> Sort u`, and given `obj : T args`,
        -- every `.proj T field obj` is equivalent to (pseudosyntax) `T.field args obj`.

        -- *Problem*: We do not have `args` in this `.proj` unfortunately, so if we encounter
        -- `.proj Prod 0 obj`, then we don't know which α and β Prod has been monomorphized to.
        -- Solution: We infer the type of `obj`, which is a bvar or fvar or const which has
        -- (hopefully) already been monomorphized.
        -- This might lead to performance problems since we call `Meta.inferType` for every projection,
        -- But I don't know of a robust quick-to-implement solution right now.
        let objType <- Meta.inferType obj'
        let .const T' _levels := objType.getAppFn 
          | throwError "Don't know how to translate projection {e}, since the type of {obj'} is not a const, but a {objType} instead."
        return .proj T' idx obj'
      | .forallE α dom@(.sort lvl@(.succ _)) _ _ => do
        -- Apply the α-trick (environment version).
        -- Add `axiom local_1337_α : Type u` to the environment to serve as our not-further-specified type stand-in,
        -- which will replace our polymorphic type α.
        -- This will enable `List α` to be monomorphized into `List_local_1337_α`.

        let levelParams <- collectLevelParams lvl
        Meta.forallBoundedTelescope e (some 1) fun vars body => do
          let α_fvar := vars[0]!
          let decl : AxiomVal := {
            name := α ++ s!"{α_fvar}" ,
            levelParams,
            type := dom,
            isUnsafe := false,
          }
          
          Lean.addDecl <| Declaration.axiomDecl decl
          -- We do not re-bind `(α : Type) -> body`, but just return the body.
          -- So the α binder is actually erased.
          let body' := body.replaceFVar vars[0]! (.const decl.name (levelParams.map Level.param))
          descend body'

      | .forallE var dom body bi => do
        let dom' <- descend dom
        HoSmt.Util.visitForall (.forallE var dom' body bi) fun _ body => do
          descend body
      | .lam var dom body bi => do
        let dom' <- descend dom
        HoSmt.Util.visitLambda' (.lam var dom' body bi) fun _ body => do
          descend body
      | _ => throwError "[Monomorphize.traverse] Don't know how to handle {e.ctorName} in {e}"

/-- Recurse through all subexpressions and replace `T U` with `T_U`, and `T.c U args` with `T_U.c args`.
  If a monomorphic variant of `T U` doesn't exist yet, it will be generated. -/
def traverse (e : Expr) : TransM Expr := traverse' e none

def traverseConst (n : Name) : TransM Name := traverseConst' n traverse'

end HoSmt.Translation.Monomorphize



