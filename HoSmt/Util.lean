import Lean
import Lean.Util.Trace
import Std.Tactic.OpenPrivate -- >:D

open Std Lean Meta Elab Tactic

namespace HoSmt.Util

def array2HashSet [Hashable α] [BEq α] (a : Array α) : HashSet α :=
  a.foldl (fun set e => set.insert e) {}

def unwrap! [Inhabited α] (o : Option α) (hint : String): α :=
  if let some val := o then val
  else
    panic! s!"UNWRAP failed: {hint}"

instance [BEq α] [Hashable α] [ToFormat α] [ToFormat β] : ToFormat (HashMap α β) where
  format (map: HashMap α β) : Format :=
    let inner : Format := map.toArray.foldl
      (fun fmt (a, b) => f!"({a} => {b}), {fmt}")
      f!""
    f!"\{{inner}}"

instance [BEq α] [Hashable α] [ToFormat α] : ToFormat (HashSet α) where
  format (set: HashSet α) : Format :=
    let inner : Format := set.toArray.foldl (fun fmt a => f!"{a}, {fmt}") f!""
    f!"\{{inner}}"

def debugLocalContext (hint : String := ""): MetaM Unit := do
  let ctx <- Lean.MonadLCtx.getLCtx
  for decl in ctx do
    let declExpr := decl.toExpr
    let declName := decl.userName
    trace[HoSmt.debug] f!"{hint} local name: {declName} === {declExpr} ::: {<- Meta.inferType declExpr}"

def todo! [Inhabited α] (message: Option String := none) : α :=
  if let some msg := message then
    panic! msg
  else
    panic! "Not yet implemented"

/-- Get a constructor from the environment-/
def TermElabM.getCtor! (name : Name) : TermElabM ConstructorVal := do
  if let ConstantInfo.ctorInfo ctor := (<- getEnv).find? name |>.get! then
    return ctor
  else
    throwError m!"No such ctor item {name} in environment"

def TermElabM.getInduct! (name : Name) : TermElabM InductiveVal := do
  if let some <| ConstantInfo.inductInfo ii := (<- getEnv).find? name then
    return ii
  else
    throwError m!"No such inductive item {name} in environment"

/-- Get a recursor for the given inductive type from the environment. -/
def TermElabM.getRec! (name : Name) : TermElabM RecursorVal := do
  let name := name ++ `rec
  if let ConstantInfo.recInfo r := (<- getEnv).find? name |>.get! then
    return r
  else
    throwError m!"No such ctor item {name} in environment"

def visitManyForall
  [Monad n]
  [MonadControlT MetaM n]
  [MonadLiftT MetaM n]
  (e : Expr) (bound: Option Nat) (f : (fvars: Array Expr) -> (body: Expr) -> n Expr) : n Expr := do
  -- un-bind the top level forall and create a new fvar for its variable.
  Meta.forallBoundedTelescope e bound <| fun vars body => do
    let res <- f vars body
    -- bind fvar again, wrapping stuff in a forall.
    let rebound <- liftM <| Meta.mkForallFVars vars res
    return rebound

/-- Update `e` (a forallE) with `f`, exposing the bound var as a fvar, and then rebinds it as a bvar afterwards.
The following is a no-op:
```lean4
visitForall e <| fun var body => do
  return body
```
 -/
def visitForall
  [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
  (e : Expr) (f : (fvar: Expr) -> (body: Expr) -> n Expr) : n Expr :=
  visitManyForall e (some 1) (fun vars body => f vars[0]! body)

/-- If `e` is a forall telescope, go through each domain, use `f_dom` to modify the domain, and then
invoke `visitForall` with `f_body` *only* when `f_dom` updated the domain
-/
partial def visitForallDomains
  [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n]
  (e : Expr)
  (f_dom: (dom: Expr) -> n (Expr × ((var:Expr) -> (body:Expr) -> n Expr)))
  -- (f_body : (fvar: Expr) -> (body : Expr) -> TermElabM Expr)
  (depth : Nat := 0)
  : n Expr
:= do
  if let .forallE faVar faDomain faBody faBi := e then
    let (newDomain, bodyUpdater) <- f_dom faDomain
    let e := .forallE faVar newDomain faBody faBi

    Meta.forallBoundedTelescope e (some 1) <| fun vars body => do
      let newbody <- bodyUpdater vars[0]! body
      let newbody <- visitForallDomains newbody f_dom (depth + 1)
      let rebound <- Meta.mkForallFVars vars newbody
      return rebound
  else
    return e

def withLambda
  [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n] [MonadNameGenerator n]
  [MonadError n] [MonadLCtx n] [MonadWithReaderOf Meta.Context n]
  (e : Expr) (f : FVarId -> Expr -> n α) : n α := do
  let .lam var ty body bi := e | throwError "not a lambda"
  let fvarId <- mkFreshFVarId
  let body := body.instantiate1 (.fvar fvarId) -- replace the now-loose bvar with our fvar
  let lctx := (<- getLCtx).mkLocalDecl fvarId var ty bi
  withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) do
    f fvarId body

/--
  The following is a no-op:
  ```
  visitLambda (λx:τ, ...) fun fv body => do
    -- Here the LocalContext is augmented by `x : τ`
    return body
  ```
-/
def visitLambda'
  [MonadControlT MetaM n] [Monad n] [MonadLiftT MetaM n] [MonadNameGenerator n]
  [MonadError n] [MonadLCtx n] [MonadWithReaderOf Meta.Context n]
  (e : Expr) (f : FVarId -> Expr -> n Expr) : n Expr
:= do
  withLambda e fun var body => do
    -- let rebound <- liftM <| Meta.mkForallFVars vars res
    let body' <- f var body
    Meta.mkLambdaFVars #[.fvar var] body'

initialize registerTraceClass `HoSmt.Util.AddDecl
initialize registerTraceClass `HoSmt.Util.registerProjFn

#check StructureInfo
#check StructureFieldInfo
/- For Reference:
structure StructureInfo where
  structName : Name
  fieldNames : Array Name := #[] -- sorted by field position in the structure
  fieldInfo  : Array StructureFieldInfo := #[] -- sorted by `fieldName`

structure StructureFieldInfo where
  fieldName  : Name
  projFn     : Name
  /-- It is `some parentStructName` if it is a subobject, and `parentStructName` is the name of the parent structure -/
  subobject? : Option Name
  binderInfo : BinderInfo
  autoParam? : Option Expr := none

structure StructureDescr where
  structName : Name
  fields     : Array StructureFieldInfo -- Should use the order the field appear in the constructor.
  deriving Inhabited

def StructureInfo.getProjFn? (info : StructureInfo) (i : Nat) : Option Name :=
  if h : i < info.fieldNames.size then
    let fieldName := info.fieldNames.get ⟨i, h⟩
    info.fieldInfo.binSearch { fieldName := fieldName, projFn := default, subobject? := none, binderInfo := default } StructureFieldInfo.lt |>.map (·.projFn)
  else none
-/

-- structure StructureLikeTranslationInfo (m) [Monad m] where
--   oldT : Name
--   registerTranslation : Name -> m Name

structure AddInductiveDeclResult where
  /-- If the original and derived type are both structures, these are the resulting projection functions. -/
  projFnsMapping : Option <| HashMap Name Name

/-- Convenience function for creating forall binders.
  For example you can create `(x : T) -> ... x ... ` (with `x` bound properly) as follows:
  ```
  createForall `x (.const T) fun x => do
    return ... x ...
  ```
-/
def createForall (varName : Name) (bi : BinderInfo := .default) (dom : Expr)
  (f : (var : Expr) -> MetaM Expr)
  : MetaM Expr
:= do
  withLocalDecl varName bi dom fun fvar => do
    let body <- f fvar
    let res <- mkForallFVars #[fvar] body
    return res

def createLambda (varName : Name) (bi : BinderInfo := .default) (dom : Expr)
  (f : (var : Expr) -> MetaM Expr)
  : MetaM Expr
:= do
  withLocalDecl varName bi dom fun fvar => do
    let body <- f fvar
    let res <- mkLambdaFVars #[fvar] body
    return res

-- structure ProjFn where
--   /-- E.g. `weight`. -/
--   fieldName : Name
--   /-- E.g. `Doughnut.weight` -/
--   projFn : Name

/-- Derives projection functions for the struct fields. The result are named of defns sorted by
  their field index. -/
partial def deriveProjFns' [Monad m]
  [MonadOptions m] [MonadLiftT IO m] [MonadTrace m]
  [AddMessageContext m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] 
  [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (structName : Name)
  : m (List StructureFieldInfo)
:= do
  let T <- getConstInfoInduct structName
  let mk <- getConstInfoCtor T.ctors[0]!
  if T.numIndices != 0 then
    trace[HoSmt.debug] "Somehow the structure {T.name} has {T.numParams} params and {T.numIndices} indices.\ninductive {T.name} : {T.type} where\n  | {mk.name} : {mk.type}"
  let isClass := Lean.isClass (<- getEnv) T.name
  forallBoundedTelescope mk.type T.numParams fun params body => do
    let Self := mkAppN (.const T.name (T.levelParams.map Level.param)) params -- T params
    withLocalDecl `self .default Self fun self => do
      go T isClass self params body 0
where
  go (T : InductiveVal) (isClass : Bool) (self : Expr) (params : Array Expr) (body : Expr) (idx : Nat) : m (List StructureFieldInfo) := do
    let .forallE fieldName F _ bi := body
      | return []
    Meta.forallBoundedTelescope body (some 1) fun vars Rest => do
      -- From `p :: P ⊢ F` and `p :: P ⊢ self`
      -- construct `⊢ (p :: P) -> (self : T p) -> F`.
      let projFnType
        <- mkForallFVars params <|
          <- mkForallFVars #[self] <|
            F -- F does not depend on `self` actually.
      -- trace[HoSmt.debug] "T.numParams = {T.numParams}, params = {params}, T.type = {T.type}"

      -- Construct `⊢ λp :: P, λself : T p, T.idx`.
      let projFnVal
        <- mkLambdaFVars params <|
          <- mkLambdaFVars #[self] <|
            Expr.proj T.name idx self

      let projFnName := T.name ++ fieldName -- T.donuts
      trace[HoSmt.Util.AddDecl] "addDecl (projection function)\ndef {projFnName} ::: {projFnType} === {projFnVal}"
      addDecl <| Declaration.defnDecl {
        name := projFnName,
        levelParams := T.levelParams,
        type := projFnType,
        value := projFnVal,
        hints := ReducibilityHints.abbrev, -- idk..
        safety := .safe, -- I sure hope so lol.
      }
      trace[HoSmt.Util.AddDecl] "successfully added ({projFnName})"
      setEnv <| Lean.addProjectionFnInfo (<- getEnv) projFnName T.ctors[0]! T.numParams idx isClass
      trace[HoSmt.Util.registerProjFn] "addProjectionFnInfo {projFnName} for ctor {T.ctors[0]!} with index {idx}"

      -- If   `p :: P             ⊢ (f : F) -> Rest`,
      -- then `p :: P, self : T p ⊢            Rest[f ↦ (Expr.proj T idx self)]`.
      -- Note: Because of this, we do *not* need the `f` on the lhs of `⊢` in `p :: P, f : F ⊢ Rest`!
      let f := vars[0]!
      let Rest' := Rest.replaceFVar f (Expr.proj T.name idx self)
      
      let sfi : StructureFieldInfo := {
        fieldName
        projFn := projFnName
        binderInfo := bi
        subobject? := none -- TODO: this should point to the parent I think, but I'm exhausted...
      }
      return sfi :: (<- go T isClass self params Rest' (idx + 1))

/--
  Add an inductive type to the environment and send it to the kernel.

  The `nRemovedParams` indicates the amount of parameters that have slid into fields.
  This happens when index erasure removes params from an inductive type, but leaves the params
  in the ctors.
  Lean interprets this as new fields.
  Therefore we need to shift the projection function indices accordingly.
-/
def addInductiveDecl
  [Monad m] [MonadOptions m] [MonadLiftT IO m] [MonadTrace m] [MonadRef m]
  [AddMessageContext m] [MonadLiftT CoreM m] [MonadEnv m] [MonadError m] [MonadLiftT BaseIO m]
  [MonadControlT MetaM m] [MonadLiftT MetaM m]
  (lparams : List Name)
  (nparams : Nat)
  (name : Name) -- newT
  (oldT : Name) -- oldT
  (type : Expr)
  (ctors : List Constructor)
  (isUnsafe := false)
  (deriveProjFns := true)
  (nRemovedParams := 0)
  : m AddInductiveDeclResult := do

  let fmtFvarsWarning : Expr -> m MessageData := fun expr => do
    let fvars := Lean.collectFVars {} expr |>.fvarIds
    let md <- fvars.foldlM (fun acc fv => do pure m!"{acc}, {(<- fv.getDecl).userName}") MessageData.nil
    if !md.isEmpty then pure m!"((!! Still have fvars {md})) "
    else pure m!""

  let mut traceMessage := m!"(numParams={nparams}) inductive {name}.\{{lparams}} : {type} {<- fmtFvarsWarning type}where\n"
  for ctor in ctors do
    traceMessage := traceMessage ++ m!"| {ctor.name} : {ctor.type} {<- fmtFvarsWarning ctor.type}\n"
  withTraceNode `HoSmt.Util.AddDecl (fun _ => pure traceMessage) do

    let decl := mkInductiveDeclEs lparams nparams [InductiveType.mk name type ctors] isUnsafe
    withLCtx {} {} do
      Lean.addDecl decl
      trace[HoSmt.Util.AddDecl] "successfully added {name}"
      Lean.mkCasesOn name
      Lean.mkNoConfusion name
      mkInjectiveTheorems name
      trace[HoSmt.Util.AddDecl] "successfully derived Lean.mkCasesOn, Lean.mkNoConfusion, mkInjectiveTheorems ({name})"

    if !deriveProjFns then return ⟨none⟩

    -- if the old type had registered structureInfo, then derive new projection functions,
    -- and register a new Structure.
    if let some oldStructInfo := Lean.getStructureInfo? (<- getEnv) oldT then
      let newProjFns : List _ <- withTraceNode `HoSmt.Util.AddDecl (fun _ => pure m!"Deriving new proj fns...") do
        deriveProjFns' name
      -- Need a mapping from oldProjFn to new projFns
      let fieldInfos' <- oldStructInfo.fieldNames.mapM fun oldFieldName => do
        let some oldFi := oldStructInfo.fieldInfo.find? (fun oldFi => oldFi.fieldName == oldFieldName)
          | throwError "bug"
        let some oldProjFn := Lean.getProjFnForField? (<- getEnv) oldT oldFi.fieldName
          | throwError "addInductiveDecl (oldT={oldT}, newT={name}): {oldT} has no proj fn for field {oldFi.fieldName} :("
        let some newProjFn := newProjFns.find? (fun sfi => sfi.fieldName == oldFi.fieldName)
          | throwError "addInductiveDecl (oldT={oldT}, newT={name}): deriveProjFns created no new projFn for old field {oldFi.fieldName} :("
        return (oldProjFn, newProjFn.projFn)
      let structDescr' : StructureDescr := {
        structName := name
        fields := newProjFns.toArray
      }
      -- TODO: return mapping of old proj fns to new proj fns
      trace[HoSmt.Util.registerProjFn] "previous {oldStructInfo.structName} has fields with proj fns: {oldStructInfo.fieldNames}"
      trace[HoSmt.Util.registerProjFn] "registerStructure {structDescr'.structName} has fields with proj fns: {structDescr'.fields.map fun x => (x.fieldName, x.projFn)}"
      setEnv <| Lean.registerStructure (<- getEnv) structDescr'
      let projFnMapping : HashMap Name Name := fieldInfos'.foldr (fun (old, new) acc => acc.insert old new) HashMap.empty
      -- if oldT == `OfNat.Erased then throwError "a, newProjFns is {newProjFns.map (fun x => m!"{x.fieldName} ↦ {x.projFn}")}, and projFnMapping is {projFnMapping}"
      return ⟨projFnMapping⟩
    else
      return ⟨none⟩

/--
  Returns true when the inductive type is for example `T : ... -> Prop`.
  This function is used in order to check whether an inductive type is an inductive predicate,
  such as `Vec.Inv`.
 -/
def isInductivePredicate (ii : InductiveVal) : TermElabM Bool := do
  Meta.forallBoundedTelescope ii.type none fun _ body => do
    return body.isProp

def ciKind: ConstantInfo -> String
| .axiomInfo    _ => "axiom"
| .defnInfo     _ => "defn"
| .thmInfo      _ => "thm"
| .opaqueInfo   _ => "opaque"
| .quotInfo     _ => "quot"
| .inductInfo   _ => "induct"
| .ctorInfo     _ => "ctor"
| .recInfo      _ => "rec"

def ConstantInfo.numParams : ConstantInfo -> Option Nat
| .inductInfo info => info.numParams
| .ctorInfo info => info.numParams
| .recInfo info => info.numParams
| _ => none

def ConstantInfo.numIndices : ConstantInfo -> Option Nat
| .inductInfo info => info.numIndices
| .recInfo info => info.numIndices
| _ => none

elab "#constant_info " n:ident rec_repr:"rec_repr"? : command => do
  let .ident _ _ name .. := n.raw | throwError "Expected identifier"
  let some ci := (<- getEnv).find? name | throwError "No such name in environment"
  match ci with
  | .inductInfo ii => logInfo m!"induct with {ii.numParams} params, and {ii.numIndices} indices"
  | .ctorInfo ctor => logInfo m!"ctor with {ctor.numParams} params, and {ctor.numFields} fields"
  | .defnInfo _ => do
    Command.liftTermElabM do
      let some eqns <- Meta.getEqnsFor? name true | throwError "No equations for this defn"
      let env <- getEnv
      let msg_eqns <- eqns.foldrM (fun eqName md => do
        let some (.thmInfo eq) := env.find? eqName | panic! s!"{eqName} is not a theorem? :("
        return m!"{md}\n\n{eqName}\n::: {eq.type}\n=== {eq.value}"
      ) m!"" 
      logInfo m!"defn (click for equations)"
      logInfo msg_eqns
  | .recInfo rec =>
    logInfo m!"rec, numParams={rec.numParams}, numIndices={rec.numIndices}, numMinors={rec.numMinors}, numMotives={rec.numMotives} (click for recursor rules)"
    Command.liftTermElabM do
      for (rule : RecursorRule) in rec.rules do
        let detailed := if rec_repr.isSome then m!"\n\n{repr rule.rhs}" else m!""
        let type : Expr <- Meta.inferType rule.rhs
        logInfo m!"+ RecursorRule \"{rule.ctor}\"\n:::{type}\n=== {rule.rhs}{detailed}"
  | _ => logInfo m!"{ciKind ci}"

def getUsedConstantsWithProj (expr : Expr) : TermElabM (HashSet Name) := do
  let rec visit  (e : Expr) (acc : HashSet Name): TermElabM (HashSet Name) := do
    -- Can't do type inferences since we have bvars...
    -- -- if e is a proof (e : _ : Prop), ignore it.
    -- if (<- Meta.inferType (<- Meta.inferType e)).isProp then
    --   return {}

    match e with
    | Expr.forallE _ d b _   => visit b (← visit d acc)
    | Expr.lam _ d b _       => visit b (← visit d acc)
    | Expr.mdata _ b         => visit b acc
    | Expr.letE _ t v b _    => visit b (← visit v (← visit t acc))
    | Expr.app f a           => visit a (← visit f acc)
    | Expr.proj T idx b      => do
      let acc <- visit b acc
      let acc := acc.insert T
      let some structInfo := Lean.getStructureInfo? (<- getEnv) T
        | throwError "encountered projectino with no associated structure info in expression {e}"
      let some projFn := structInfo.getProjFn? idx
        | throwError "{T} has no proj fn with idx {idx}"
      let acc := acc.insert projFn
      return acc
    | Expr.const c _         => return acc.insert c
    | _ => return acc
  let set <- visit expr {}
  return set

/-- Just like `Expr.getUsedConstants`, but for any environment items.

  Uses `Meta.getEqnsFor?` instead of the raw `.value`.
  And then only uses the type of those equations, not their proof.

  Discards proofs of theorems.
 -/
def ConstantInfo.getUsedConstantsClean (ci : ConstantInfo) (equations : HashMap Name (HashSet Name)) : TermElabM (HashSet Name) := do
  let mut ret <- go ci
  let equations := equations.findD ci.name {}
  for extra in equations do
    let some ci := (<- getEnv).find? extra
      | throwError "no such const {extra}"
    ret := ret.insertMany (<- go ci)
  ret := ret.erase ci.name
  return ret
where
  go : ConstantInfo -> TermElabM (HashSet Name)
  | .inductInfo ii => do
    let mut set <- getUsedConstantsWithProj ii.type --:= array2HashSet ii.type.getUsedConstants
    for ctor in ii.ctors do
      let ctor <- TermElabM.getCtor! ctor
      set := set.insertMany <| <- getUsedConstantsWithProj ctor.type -- ctor.type.getUsedConstants
    return set.erase ii.name
  | .defnInfo di => do
    if let some eqns := (<- Meta.getEqnsFor? di.name) then
        -- | throwError "Can't derive equations ('match') for defn {di.name}"
      let mut set := {}
      for eqName in eqns do
        let some (.thmInfo ti) := (<- getEnv).find? eqName | throwError "No such equation {eqName}"
        set := set.insertMany <| <- getUsedConstantsWithProj ti.type -- ti.type.getUsedConstants
      return set
    else
      let mut set := {}
      set := set.insertMany <| <- getUsedConstantsWithProj di.type -- di.type.getUsedConstants
      set := set.insertMany <| <- getUsedConstantsWithProj di.value -- di.value.getUsedConstants
      return set
  | .thmInfo ti => do
    -- Ignore the proof.
    getUsedConstantsWithProj ti.type -- ti.type.getUsedConstants
  -- | .recInfo ri => sorry
  | ci => do
    let mut set <- getUsedConstantsWithProj ci.type -- := array2HashSet ci.type.getUsedConstants
    if let some value := ci.value? then
      set := set.insertMany <| <- getUsedConstantsWithProj value -- value.getUsedConstants
    return set

/-- `[]` gives `""`, `["a", "b"]` gives `"a, b"`. -/
def join_delim (delim: String := ", ") : List String -> String
| [] => ""
| [last] => last
| x :: (y :: tail) => x ++ delim ++ (join_delim delim (y :: tail))

def HashSet.fromList [BEq α] [Hashable α] : List α -> HashSet α
| [] => {}
| x :: xs => fromList xs |>.insert x

/-- Like `withMainContext`, but is more compatible with other monads. -/
def withMainContext' [Monad m] [MonadControlT MetaM m] [MonadLiftT TacticM m] (x : m α) : m α := do
  let mainGoal <- getMainGoal
  mainGoal.withContext x

elab "#isDefEq " t₁:term "===" t₂:term : command => do 
  Command.liftTermElabM do
    let e₁ <- Lean.Elab.Term.elabTerm t₁ none
    let e₂ <- Lean.Elab.Term.elabTerm t₂ none
    -- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/isDefEq.20thing.20I.20dont.20understand
    Term.synthesizeSyntheticMVarsUsingDefault
    let isEq <- Lean.Meta.isDefEq e₁ e₂
    logInfo s!"{isEq}"

partial def Range.map (range : Std.Range) (f : Nat -> α) : List α :=
  if range.start >= range.stop then []
  else f range.start :: (Range.map { range with start := range.start + range.step } f)

partial def List.repeat (list : List α) (times : Nat) : List α :=
  match times with
  | 0 => []
  | .succ n => list ++ (List.repeat list n)

elab "#itemDepsForHoSmt " name:ident : command => do
  let .ident _ _ name .. := name.raw | throwError "Expected identifier"
  let env <- getEnv
  let some ci := env.find? name | throwError "oh no"
  Command.liftTermElabM do
    let directDeps <- ConstantInfo.getUsedConstantsClean ci {}
    logInfo m!"{directDeps}"

#itemDepsForHoSmt Nat.add
#itemDepsForHoSmt List.map -- no recursor, since it collects deps from eqns

/-- Replace all occurences of constant `old` with `new` in the entire expression. -/
partial def replaceConstEnv (old : Name) (new : Expr) (expr : Expr) : Expr :=
  let go := replaceConstEnv old new
  match expr with
  | .forallE var dom body bi => .forallE var (go dom) (go body) bi
  | .const name levels => if name == old then new else .const name levels
  | .app f a => .app (go f) (go a)
  | .lam var dom body bi => .lam var (go dom) (go body) bi
  | .letE var dom value body nondep => .letE var (go dom) (go value) (go body) nondep
  -- | .proj name idx val => .proj (if name == old then new else name) idx val
  | _ => expr

/-- Replace all occurences of constant `old` with `new` in the entire expression. -/
partial def replaceConst (old : Name) (new : Name) (expr : Expr) : Expr :=
  let go := replaceConst old new
  match expr with
  | .forallE var dom body bi => .forallE var (go dom) (go body) bi
  | .const name levels => .const (if name == old then new else name) levels
  | .app f a => .app (go f) (go a)
  | .lam var dom body bi => .lam var (go dom) (go body) bi
  | .letE var dom value body nondep => .letE var (go dom) (go value) (go body) nondep
  | .proj name idx val => .proj (if name == old then new else name) idx val
  | _ => expr

/-- Replace all occurences of constant `old` with `new` in the entire expression. -/
partial def replaceConst' (old : Name) (new : Expr) (expr : Expr) : Expr :=
  let newName := new.constName!
  let go := replaceConst' old new
  match expr with
  | .forallE var dom body bi => .forallE var (go dom) (go body) bi
  | .const name _ => if name == old then new else expr
  | .app f a => .app (go f) (go a)
  | .lam var dom body bi => .lam var (go dom) (go body) bi
  | .letE var dom value body nondep => .letE var (go dom) (go value) (go body) nondep
  | .proj name idx val => .proj (if name == old then newName else name) idx val
  | _ => expr

/-- If this ConstantInfo has a value, applies `f` on it and returns the modified constant info. -/
def ConstantInfo.modifyValue [Monad m] (ci : ConstantInfo) (f : Expr -> m Expr) : m ConstantInfo := do
  match ci with
  | .defnInfo di => return .defnInfo { di with value := <- f di.value }
  | .thmInfo ti => return .thmInfo { ti with value := <- f ti.value }
  | _ => return ci

private def levelParamCollector [Monad m] (type : Expr) (value : Option Expr) : m (List Name) := do
  let ret := value.map (Lean.collectLevelParams {}) |>.getD {}
  return Lean.collectLevelParams ret type |>.params |>.toList

/--
  Modifies the type and value of this definition-like (definition, theorem, or axiom) constant.
  By default, simply collects all remaining levelParams from the resulting type and value.
  Doesn't work with mutual blocks.

  Also returns whether there has been any change.

  - `recAsAxiom`: If `ci` is a `.recInfo`, then also translate the recursor, but add it as an
    axiom instead.
  - `skipRecs`: If the body contains `*.rec` or `*.X` where X is an auxiliary recursor (`brecOn`,
    `casesOn`, ...), replaces the body with `sorryAx`.
  - `sorryOnFailure`: If translating the body fails for whatever reason, just replace it with `sorryAx`.
    This check is done after `skipRecs`.
-/
def ConstantInfo.modify [Monad m] [MonadError m] [MonadMCtx m] [MonadLiftT MetaM m] [MonadEnv m]
  (ci : ConstantInfo)
  (name' : Name)
  (fType : Expr -> m Expr)
  (fVal : Expr -> m Expr)
  (recAsAxiom : Bool := true)
  (skipRecs : Bool := true)
  (sorryOnFailure : Bool := false)
  (fLevelParams : (type' : Expr) -> (value' : Option Expr) -> m (List Name) := levelParamCollector)
  : m (ConstantInfo × Bool) := do
  match ci with
  | .defnInfo { all, type, value, hints, safety, name := oldName, .. } =>
    if all.length != 1 then throwError "Mutually inductive defns not supported."
    let type' <- fType type
    let mut value' := value
    let env <- getEnv

    let consts := value'.getUsedConstants
    if skipRecs then
      if consts.any (fun c => Lean.isAuxRecursor env c || Lean.isRecCore env c) then
        value' <- Meta.mkSorry type' true

    -- this is so ugly, and more of a hack, but it's late... ;-;
    if consts.contains ``sorryAx then
      -- propagate `sorry`. Necessary since otherwise monomorphization code attempts `applyLambdasPattern`,
      -- but instead of lambdas it encounters a sorry and explodes.
      value' <- Meta.mkSorry type' true
    else
      try
        value' <- fVal value'
      catch ex => do
        if sorryOnFailure then
          value' <- Meta.mkSorry type' true
        else
          throw ex

    let levelParams <- fLevelParams type' value'
    -- replace recursive usages (not sure if this is the right way..)
    let value₂ := replaceConst' oldName (.const name' (levelParams.map Level.param)) value'
    let _ <- isDefEq type' (<- inferType value₂)
    let defn := .defnInfo {
      name := name'
      all := [name']
      levelParams
      type := <- instantiateMVars type'
      value := <- instantiateMVars value₂
      hints
      safety
    }
    return (defn, type != type' || value != value')
  | .thmInfo { type, all, .. } => do
    if all.length != 1 then throwError "Mutually inductive theorems not supported."
    let type' <- fType type
    let value' <- Meta.mkSorry type' true -- Just ignore the proofs.
    -- let value' <- try
    --     fVal value
    --   catch ex => do
    --     if sorryOnFailure then
    --       Meta.mkSorry type' true
    --     else
    --       throw ex
    let thm := .thmInfo {
      name := name'
      all := [name']
      levelParams := <- fLevelParams type' value'
      type := <- instantiateMVars type'
      value := <- instantiateMVars value'
    }
    return (thm, type != type')
  | .axiomInfo { type, isUnsafe, .. } => do
    let type' <- fType type
    let ax := .axiomInfo {
      name := name'
      levelParams := <- fLevelParams type' none
      type := <- instantiateMVars type'
      isUnsafe
    }
    return (ax, type != type')
  | .recInfo { type, isUnsafe, .. } => do
    if recAsAxiom then
      let type' <- fType type
      let ax := .axiomInfo {
        name := name'
        levelParams := <- fLevelParams type' none
        type := <- instantiateMVars type'
        isUnsafe
      }
      return (ax, type != type')
    else
      throwError "modifying {ciKind ci} not supported"
  | .quotInfo info => return (.quotInfo info, false)
  | _ => throwError "modifying {ciKind ci} not supported"

/-- Replaces the body with a `sorry`, if this is a definition or theorem. -/
def ConstantInfo.removeBody : ConstantInfo -> MetaM ConstantInfo
| .thmInfo info => return .thmInfo { info with value := <- Meta.mkSorry info.type true }
| .defnInfo info => return .defnInfo { info with value := <- Meta.mkSorry info.type true }
| x => return x

def ConstantInfo.toDefnLikeDecl [Monad m] [MonadError m] (ci : ConstantInfo) : m Declaration := do
  match ci with
  | .defnInfo info => return .defnDecl info
  | .thmInfo info => return .thmDecl info
  | .axiomInfo info => return .axiomDecl info
  | _ => throwError "Can't convert ci {ci.name} (which is a {ciKind ci}) to a Declaration."

def collectLevelParams (lvl : Level) : MetaM (List Name) := do
  return (<- go lvl).toList
where
  go : Level -> MetaM (HashSet Name)
  | .zero => return {}
  | .succ lvl => go lvl
  | .max a b => return (<- go a) |>.insertMany (<- go b)
  | .imax a b => return (<- go a) |>.insertMany (<- go b)
  | .param name => return HashSet.empty.insert name
  | .mvar id => throwError "collecting level params encountered mvar {repr id}"

/-- Checeks whether a given inductive type has no indices or type params.
For example `List` is not a simple type, but `Nat` is. -/
def isSimpleType (expr : Expr) : MetaM Bool := do
  let some (name, _) := expr.const? | return false
  let some ci := (<- getEnv).find? name | return false
  match ci with
  | .inductInfo ii =>
    return ii.numParams == 0 && ii.numIndices == 0
  | .axiomInfo ai =>
    -- For α-trick: Axioms such as `axiom local_1337_α : Type u` are simple, but not-further-specified, types.
    return ai.type.isType
  | _ => return false

def reduceLet : Expr -> Expr
| .letE _var _ty value body _nonDep => body.instantiate1 value
| e => e

end HoSmt.Util