import Lean
import Lean.Data
import HoSmt.Translation.TransM
import HoSmt.Translation.OccurenceRewriting
import HoSmt.Translation.Patterns
import HoSmt.Util

open Lean Elab Term Command Tactic Expr Std Meta
open HoSmt.Translation.TransM HoSmt.Util TermElabM HoSmt.Translation.OccurenceRewriting
open HoSmt.Translation.Patterns

namespace HoSmt.Translation.IndexErasure
/-!
  An implementation an extension of the Nunchaku rule to erasing type indices in CIC types.
-/

initialize Lean.registerTraceClass `HoSmt.Translation.IndexErasure
initialize Lean.registerTraceClass `HoSmt.Translation.IndexErasure.traverse
initialize Lean.registerTraceClass `HoSmt.Translation.IndexErasure.traverseConst
initialize Lean.registerTraceClass `HoSmt.Translation.IndexErasure.mkEtype

def primitives := [``Subtype]

/--
  Given a forall telescope such as `(a :: A) -> Sort u`, returns a tuple of:
  - The erased type with fewer binders.
  - The pattern of which binders were removed.
-/
private partial def mkEtype (numParams : Nat) (e : Expr) : TransM (Expr × List Bool) := do
  let log
  | .ok (expr, pat) => return m!"mkEtype numParams={numParams}, {e} ~~> ({pat}, {expr})"
  | .error ex => return m!"mkEtype numParams={numParams}, {e} ~~> error, {ex.toMessageData}"
  withTraceNode `HoSmt.Translation.IndexErasure.mkEtype log do
    if numParams == 0 then
      Meta.forallBoundedTelescope e none fun vars body =>
        return (body, List.repeat [true] vars.size)
    else
      match e with
      | .forallE _ dom .. => do
        Meta.forallBoundedTelescope e (some 1) fun vars body => do
          let (body', pat) <- mkEtype (numParams - 1) body
          -- trace[HoSmt.Translation.IndexErasure.mkEtype] "dom repr is {repr dom}, and isType = {dom.consumeTypeAnnotations.isType}"
          if dom.consumeTypeAnnotations.isSort then
            -- `(_ : Type) -> ...` binder (TU), do not erase.
            return (<- mkForallFVars #[vars[0]!] body', false :: pat)
          else
            -- VU binder, erase it.
            return (body', true :: pat)
      | .sort .. => return (e, [])
      | _ => throwError "[mkEtype] Expected forall telescope terminated by sort, but got {e}"

class MkApp (α : Type) where
  betterMkApp : α -> Array Expr -> TransM Expr
instance: MkApp Name where
  betterMkApp (n : Name) (args : Array Expr) := do
    mkAppOptM n (args.map Option.some)
instance: MkApp Expr where
  betterMkApp (fn : Expr) (args : Array Expr) := do
    mkAppOptM' fn (args.map Option.some)
open MkApp

/-- Transform `(x : T u i) -> Rest` into `(x : E u) -> G u i x -> Rest` -/
private def rewriteBinder [MkApp α] [MkApp β] (expr : Expr) (T : Name) (E : α) (G : β) (pattern : List Bool) : TransM Expr := do
  if let .forallE var dom body bi := expr then
    if dom.isAppOf T then -- expr === (x : T u i) -> Rest
      let u_i := dom.getAppArgs
      -- E u
      let erased <- betterMkApp E ((<- filterByPatternInv u_i.toList pattern).toArray)
      -- transform `(x : E u) -> Rest` into `(x : E u) -> G u i x -> Rest`
      return <- Util.visitForall (.forallE var erased body bi) fun x Rest => do
        return .forallE `guard (<- betterMkApp G (u_i ++ #[x])) Rest .default -- no need for mkForallFVars since nothing in body depends on guard.
  -- do nothing if we didn't find a `T u i` binder.
  return expr

/-- Splits a type T into its type-index erased E part and a guarding predicate G. -/
def eraseIndices (TName : Name) : TransM IndexErasureInfo := do
  if primitives.contains TName then return .notNecessary
  let T <- getConstInfoInduct TName
  -- Ignore inductive predicates `... -> Prop`
  if <- Meta.forallBoundedTelescope T.type none fun _ finalSort => pure finalSort.isProp then
    return .notNecessary

  if let some info := <- checkXEcache T.name then
    return info

  -- # Introduce type-index-erased E
  let (EType, pattern) <- mkEtype T.numParams T.type
  assert! (EType == T.type) == (pattern.all not)
  if EType == T.type then
    -- No need to erase anything
    registerXEcache T.name .notNecessary
    return .notNecessary
  let EName := T.name ++ `Erased
  let ELevelParams : List Name := Lean.collectLevelParams {} EType |>.params |>.toList
  let log
  | .ok .notNecessary => unreachable! 
  | .ok (.erased E G pat nRemovedParams) => return m!"Erasing indices of {Expr.const T.name (T.levelParams.map Level.param)} ~~> ({E}, {G}, {pat}, nRemovedParams={nRemovedParams})"
  | .error error => return m!"Erasing indices of {Expr.const T.name (T.levelParams.map Level.param)} ~~> ERROR, {error.toMessageData}"
  withTraceNode `HoSmt.Translation.IndexErasure log do
    trace[HoSmt.Translation.IndexErasure] "pattern={pattern}, ELevelParams={ELevelParams}, EType is {EType},"
    let ECtors : List Constructor <- T.ctors.mapM fun TCtorName => do
      let TCtor <- getCtor! TCtorName
      let log
      | .ok res => return m!"Deriving erased ctor from {Expr.const TCtorName (T.levelParams.map Level.param)} ~~> {res.name} : {res.type}"
      | .error error => return m!"Deriving erased ctor from {Expr.const TCtorName (T.levelParams.map Level.param)} ~~> error, {error.toMessageData}"
      withTraceNode `HoSmt.Translation.IndexErasure log do
        Meta.withLocalDeclD EName EType fun E => do
          -- Replace `T u i` with `E u` in the ctor
          let ECtorType <- descendingRewriter' TCtor.type fun expr => do
            if expr.isAppOf T.name then
              let args := expr.getAppArgs
              return mkAppN E ((<- filterByPatternInv (args.toList) pattern).toArray)
            else return expr
          return { name := TCtor.name ++ `erased, type := ECtorType.replaceFVar E (.const EName (ELevelParams.map Level.param)) }
    let ENumParams := pattern.toArray[:T.numParams].toArray.filter not |>.size -- count non-erased params. FIXME: This assumes non-erased params are a prefix.
    assert! pattern.toArray[ENumParams:].toArray.all id -- re: the fixme above ^
    let addDeclResult₁ <- addInductiveDecl ELevelParams ENumParams EName T.name EType ECtors (nRemovedParams := (T.numParams - ENumParams))

    -- # Introduce guarding predicate G
    let GName := T.name ++ `Guard

    let log
    | .ok res => return m!"Deriving GType ~~> {res}"
    | .error error => return m!"Deriving GType ~~> ERROR, {error.toMessageData}"
    let GType <- withTraceNode `HoSmt.Translation.IndexErasure log do
      -- from `T : U -> I -> Type` construct `G : U -> I -> (target : E u) -> Prop`
      Util.visitManyForall T.type none fun vars _ => do
        return mkForall `target .default
          (mkAppN (.const EName (ELevelParams.map Level.param)) ((<- filterByPatternInv vars.toList pattern).toArray)) <|
            .sort .zero
    let GLevelParams := Lean.collectLevelParams {} GType |>.params |>.toList
    
    -- Inside each ctor, do two things:
    -- 1) Do the target/final thing,
    -- 2) Replace `(x : T u i) -> Rest` with `(x : E u) -> G u i x -> Rest`.
    let GCtors : List Constructor <- T.ctors.mapM fun TCtorName => do
      let TCtor <- getCtor! TCtorName
      let ECtorName := TCtorName ++ `erased
      let ECtor := Expr.const ECtorName (ELevelParams.map Level.param)
      let log
      | .ok res => return m!"Deriving guard ctor from {TCtorName} : {TCtor.type} ~~> {res.name} : {res.type}"
      | .error error => return m!"Deriving guard ctor from {TCtorName} : {TCtor.type} ~~> error, {error.toMessageData}"
      withTraceNode `HoSmt.Translation.IndexErasure log do
        Meta.withLocalDeclD GName GType fun G => do
          -- ## Do the ctor target/final thing
          -- `... -> T u i
          -- into
          -- `... -> G u i (E.ctor u i)`
          --                ^^^^^^^^^^   <- target
          --         ^^^^^^^^^^^^^^^^^^  <- final
          let GCtor₁ <- visitManyForall TCtor.type none fun vars body => do
            -- let target := mkAppN ECtor ((<- filterByPatternInv vars.toList pattern).toArray)
            let target := mkAppN ECtor vars
            let final := mkAppN G (body.getAppArgs ++ #[target])
            trace[HoSmt.Translation.IndexErasure] "vars = {vars}"
            trace[HoSmt.Translation.IndexErasure] "body = {body}"
            return final

          -- ## Replace occurences of `(x : T u i) -> Rest` with `(x : E u) -> G u i x -> Rest`.
          let GCtor₂ <- descendingRewriter' GCtor₁ (rewriteBinder . T.name EName G pattern)

          return { name := TCtorName ++ `guard, type := GCtor₂.replaceFVar G (.const GName (GLevelParams.map Level.param)) }
    let addDeclResult₂ <- addInductiveDecl GLevelParams T.numParams GName T.name GType GCtors (deriveProjFns := false)

    let ret := .erased EName GName pattern (T.numParams - ENumParams)
    registerXEcache T.name ret
    return ret

/--
  Given an expression `T u i`, constructs `{ t : E u // G u i t }`.
-/
def mkSubtype (expr : Expr) (E G : Name) (pattern : List Bool) (hackyLevels : List Level) : TransM Expr := do
  let args := expr.getAppArgs -- u i
  let u := (<- filterByPatternInv args.toList pattern).toArray
  let E := .const E hackyLevels
  -- λtarget : E u, G u i target
  let p <- Meta.withLocalDeclD `target (mkAppN E u) fun target => do
    let guit := mkAppN (.const G hackyLevels) (args ++ #[target])
    mkLambdaFVars #[target] guit
  -- return mkApp2 (.const ``Subtype hackyLevels) (mkAppN E u) p
  mkAppOptM ``Subtype #[mkAppN E u, p]

/--
  Given an expression `T.ctor u args` typed `T u i`, constructs
  `@Subtype.mk (E u) (λtarget : G u i target) (E.ctor u args) sorry`.
-/
def mkSubtypeVal (expr : Expr) (E G : Name) (pattern : List Bool) (hackyLevels : List Level) : TransM Expr := do
  let type <- inferType expr -- T u i
  -- assert! that type actually isAppOf T
  let u := (<- filterByPatternInv type.getAppArgs.toList pattern)
  let Eex := .const E hackyLevels
  let Gex := .const G hackyLevels
  let gui := mkAppN Gex type.getAppArgs
  -- λtarget : E u, G u i target    ::: E u -> Prop
  let p <- Meta.withLocalDeclD `target (mkAppN Eex u.toArray) fun target => do
    mkLambdaFVars #[target] (.app gui target)
  
  let ECtorName := expr.getAppFn.constName! ++ `erased
  let ECtorArgs : Array Expr <- expr.getAppArgs.mapM fun arg => do
    -- if `arg : { E // G }`, then replace it with `arg.val : E`.
    let ty <- inferType arg
    if ty.isAppOf ``Subtype then
      let args := ty.getAppArgs
      if args[0]!.isAppOf E then
        return .proj ``Subtype 0 arg -- arg.val
    return arg
  let val := mkAppN (.const ECtorName hackyLevels) ECtorArgs -- `T.ctor a` ↦ `E.ctor a`

  let args := #[mkAppN Eex u.toArray, p, val, <- mkSorry (p.beta #[val]) false]
  mkAppOptM ``Subtype.mk (args.map Option.some)

def idPre (e : Expr) : TransM Expr := pure e

mutual
partial def traverseConst (const : Name) : TransM IndexErasureTraversalInfo := do
  if let some trInfo := <- checkXETcache const then return trInfo
  let some ci := (<- getEnv).find? const | throwError "no such const {const}"
  let log
  | .ok (.changed res _) => return m!"Traversing const [{ciKind ci}] {Expr.const const (ci.levelParams.map Level.param)} ~~> {res}"
  | .ok .notNecessary =>    return m!"Traversing const [{ciKind ci}] {Expr.const const (ci.levelParams.map Level.param)} ~~> (not necessary, just same {const})"
  | .error error =>         return m!"Traversing const [{ciKind ci}] {Expr.const const (ci.levelParams.map Level.param)} ~~> ERROR, {error.toMessageData}"
  withTraceNode `HoSmt.Translation.IndexErasure.traverseConst log do
    let result <- go ci
    registerXETcache const result
    if let .changed name' _ := result then
      let equations := (<- get).equations.findD const {} |>.toArray
      let equations' : Array Name <-
        if !equations.isEmpty then
          withTraceNode `HoSmt.Translation.IndexErasure.traverseConst (fun res => do return m!"traverseConst({const} ↦ {name'}) {name'} has equations: {equations} ~~> {if let .ok res := res then m!"{res}" else "error"}") do
            equations.mapM (fun extra => do return ((<- traverseConst extra).getD extra))
        else pure #[]
      registerEquations name' (some equations')
    return result
where
  go : ConstantInfo -> TransM IndexErasureTraversalInfo
  | .inductInfo info => do
    let type' <- traverse info.type idPre info.name
    let ctors' : List (Name × Expr × Bool) <- info.ctors.mapM fun ctor => do
      let ctorInfo <- getConstInfoCtor ctor
      let ctorType' <- traverse ctorInfo.type idPre info.name
      return (ctor, ctorType', ctorInfo.type != ctorType')
    if info.type != type' || ctors'.any (fun (_, _, changed) => changed) then
      let uniq <- mkFreshId
      let lparams := collectLevelParams {} type' |>.params |>.toList
      let ctors' := ctors'.map (fun (name, ty, _) => ⟨
        name ++ uniq,
        replaceConst' info.name (.const (info.name ++ uniq) (lparams.map Level.param)) ty
      ⟩)
      let addInductiveResult <- addInductiveDecl lparams info.numParams (info.name ++ uniq) info.name type' ctors'
      return .changed (info.name ++ uniq) uniq
    else
      return .notNecessary
  | .ctorInfo info => do
    if let .erased E G pattern _ := <- eraseIndices info.induct then
      -- Since we just leave the params in, we don't have to do anything other than change the name...
      return .changed (info.name ++ `erased)
      -- throwError "replace T.ctor with E.ctor..."
    else if let .changed T' uniq := <- traverseConst info.induct then
      let some uniq := uniq | throwError "Induct types need to provide their uniq suffix in IndexErasureTraversalInfo"
      return .changed (info.name ++ uniq)
      -- throwError "Also handle ctors of inductive types resulting from traversal!"
    else
      return .notNecessary
  -- | .recInfo _ => return .notNecessary
  | ci => do
    ensureHasEqns ci.name
    if ci.name == ``sorryAx then
      return .notNecessary
    let traverse := (traverse . idPre ci.name)
    let uniq <- mkFreshId
    let name' := ci.name ++ uniq
    let (ci', changed) <- ConstantInfo.modify ci name' traverse traverse
    if changed then
      addDecl <| <- ConstantInfo.toDefnLikeDecl ci'
      return .changed ci'.name
    else
      return .notNecessary

partial def traverse (e : Expr) (pre : Expr -> TransM Expr) (doNotDescend : Option Name := none) : TransM Expr := do
  let traverse := (traverse . pre doNotDescend) -- shadow trick to avoid typing doNotDescend everywhere :)
  antiStackOverflow do
    let log
    | .ok expr => return m!"Traversing {e}{if let .proj T idx obj := e then m!" (Expr.proj {T} {idx} _)" else m!""} ~~> {expr} {if let .proj T idx obj := expr then m!" (Expr.proj {T} {idx} _)" else m!""}"
    | .error error => return m!"Traversing {e}{if let .proj T idx obj := e then m!" (Expr.proj {T} {idx} _)" else m!""} ~~> error, {error.toMessageData}"
    withTraceNode `HoSmt.Translation.IndexErasure.traverse log do
      let e := e.consumeTypeAnnotations
      let e <- pre e

      -- special handling for OfNat (very hacky).
      let e := if e.isAppOf ``OfNat.ofNat && e.getAppArgs[0]? == some (.const ``Nat []) then
        if let some nat := e.getAppArgs[1]? then
          nat
        else e
      else e

      let e <- Meta.withReducible <| Meta.whnf e

      match e with
      | .app f a => do
        if let .const fn levels := e.getAppFn then
          let some ci := (<- getEnv).find? fn | throwError "No such constant {fn}"
          match ci with
          | .inductInfo info => do
            if let .erased E G pattern _ := <- eraseIndices info.name then
              -- let tmp <- rewriteBinder e info.name E G pattern
              let tmp <- mkSubtype e E G pattern levels
              return <- traverse tmp
          | .ctorInfo info =>
            if let .erased E G pattern _ := <- eraseIndices info.induct then
              -- e === `T.ctor u a`, so create `E.ctor u a`
              let tmp <- mkSubtypeVal e E G pattern levels
              -- let tmp <- betterMkApp E e.getAppArgs
              return <- traverse tmp
          | _ => pure ()
        return .app (<- traverse f) (<- traverse a)
      | .forallE var dom body bi => do
        -- This would be wrong:
        -- -- If dom changes into a subtype, then inside body we need to replace `var` with `var.val`.
        -- if let .const name levels := dom.getAppFn then
        --   if let .erased E G pattern _ := <- eraseIndices name then
        --     return <- visitForall (Expr.forallE var (<- mkSubtype e E G pattern levels) body bi) fun fv body => do
        --       let body' := body.replaceFVar fv (.proj ``Subtype 0 fv)
        --       traverse body'

        -- otherwise, just descend
        let dom' <- traverse dom
        visitForall (.forallE var dom' body bi) fun _var body => do
          traverse body
      | .lam var dom body bi => do
        -- This would be wrong:
        -- -- If dom changes into a subtype, then inside body we need to replace `var` with `var.val`.
        -- if let .const name levels := dom.getAppFn then
        --   if let .erased E G pattern _ := <- eraseIndices name then
        --     return <- visitLambda' (Expr.lam var (<- mkSubtype e E G pattern levels) body bi) fun fv body => do
        --       let body' := body.replaceFVarId fv (.proj ``Subtype 0 (.fvar fv))
        --       traverse body'
        let dom' <- traverse dom
        HoSmt.Util.visitLambda' (.lam var dom' body bi) fun _var body => do
          traverse body
      | .const name levels => do
        if some name == doNotDescend then
          return e
        else
          let name' := match <- traverseConst name with
          | .notNecessary => name
          | .changed name' _ => name'
          return .const name' levels -- TODO: fix levels
      | .fvar .. => return e
      | .mvar .. => return e
      | .lit .. => return e
      | .sort .. => return e
      | .proj T idx obj => do
        trace[HoSmt.debug] "This is a projection {repr e}"
        let obj₁ <- traverse obj
        if let .erased E _ _ nRemovedParams := <- eraseIndices T then
          -- If `obj : T u i` before erasure, then now it has become `obj₁ : { t : E u // G u i t }`.
          -- Therefore, `obj₂ := obj₁.val` will give us `obj₂ : E u`.
          let obj₂ := .proj ``Subtype 0 obj₁
          -- When we erase indices `i`, we *leave them inside the ctors*.
          -- This effectively "shifts" parameters into becoming fields. Thus we need to offset idx.
          let mut e' := .proj E (idx + nRemovedParams) obj₂ -- e' : typeof(E.fieldᵢ)
          if nRemovedParams > 0 then
            -- **Hack**: If the field is a subtype, re-sorry it.
            if let some (hack_α, hack_p) := (<- inferType e').app2? ``Subtype then
              -- from `x.1.i` build `⟨x.1.i.1, sorry⟩`
              let tmp := mkAppN (Expr.const ``Subtype.mk [<- mkFreshLevelMVar]) #[
                hack_α,
                hack_p,
                Expr.proj ``Subtype 0 e',
                <- mkSorry (<- mkFreshTypeMVar) false
              ]
              -- let derp <- inferType tmp
              e' <- instantiateMVars tmp -- Can't know the necessary type until we try to add the containing definition...
              -- throwError "Applying hack to {T}, have derp === {derp}, and e' === {e'}"
          return <- traverse e'
        else if let .changed T' _ := <- traverseConst T then
          return .proj T' idx obj₁
        else
          return .proj T idx obj₁
        -- throwError "Encountered {repr e}, whose type is {<- inferType e}, and whose obj has type {<- inferType obj}"
      | .mdata md inner => return .mdata md (<- traverse inner)
      | .letE _ _ val body _ => return <- traverse <| body.instantiate1 val -- reduce lets
      | _ => throwError "type indices: traverse Expr.{e.ctorName} unsupported with expr {e}"
end

end HoSmt.Translation.IndexErasure
