import Lean
import Lean.Data
import HoSmt.Util

open Lean Elab Std Tactic

namespace HoSmt.TPTP

initialize registerTraceClass `HoSmt.Encoding.appendItem
initialize registerTraceClass `HoSmt.Encoding.defEqns
initialize registerTraceClass `HoSmt.Encoding.inj
initialize registerTraceClass `HoSmt.Encoding
initialize registerTraceClass `HoSmt.Encoding.traverse

def primitives := [``outParam, ``optParam,
  ``Eq, ``HEq, ``Iff, ``Iff.mp, ``Iff.mpr, ``Bool, ``true, ``false, ``Not, ``And, ``Or, ``Exists,
  ``sorryAx, 
  ``Subtype, ``Subtype.mk, ``Subtype.val, ``Subtype.property,
  ``Decidable, ``Decidable.isTrue, ``Decidable.isFalse
]

section Data

/-- TPTP builtin types -/
inductive Typ where
  | SBool: Typ -- $oType, $o
  | SIndex: Typ -- $iType, $i
  | SInt: Typ -- $int
  | SType: Typ -- $tType, the "Type" of TPTP.
  | SAbstr: Typ -> Typ -> Typ -- `a -> b` in Lean, or `T > U` in TPTP.
  | SCustom : String -> Typ -- `nat` for example.
deriving Inhabited, Repr

mutual
  inductive Term where
    --- Either a *g*lobal or *V*ariable.
    | const : String -> Term
    --- λvar : T. body
    | abstr: (var: String) -> (type: Typ) -> (body: Term) -> Term
    --- Function application, `f arg`.
    | app: (f: Term) -> (arg: Term) -> Term
    --- 1337.
    | lit: Int -> Term
    | fml : Formula -> Term
  deriving Inhabited, Repr

  inductive Formula where
    | not: Formula -> Formula
    | and: Formula -> Formula -> Formula
    | or: Formula -> Formula -> Formula
    | implies: Formula -> Formula -> Formula
    | lit: Bool -> Formula
    | eq: Formula -> Formula -> Formula
    | qforall: String -> Option Typ -> Formula -> Formula
    | exists: String -> Option Typ -> Formula -> Formula
    | app : Formula -> Formula -> Formula
    | const : String -> Formula
    | var : String -> Formula
    | term : Term -> Formula
  deriving Inhabited, Repr
end

class ToTPTP (α: Type) where
  to_tptp (self: α) : String

instance (priority := low) [ToTPTP α]: ToMessageData α where
  toMessageData x := ToTPTP.to_tptp x

open ToTPTP

instance: ToTPTP Bool where
  to_tptp : Bool -> String
    | true => "$true"
    | false => "$false"

open Typ in
def Typ.to_tptp: Typ -> String
  | SBool => "$o"
  | SCustom s => s
  | SIndex => "$i"
  | SInt => "$int"
  | SType => "$tType"
  | SAbstr a b => s!"({to_tptp a} > {to_tptp b})"

instance: ToTPTP Typ where
  to_tptp : Typ -> String := Typ.to_tptp

mutual
  partial def Term.to_tptp : Term -> String
    | Term.app f t => s!"({Term.to_tptp f} @ {Term.to_tptp t})"
    | Term.const name => name
    | Term.abstr var ty body => s!"(^[{var} : {Typ.to_tptp ty}]: {Term.to_tptp body})"
    | Term.lit n => s!"{n}"
    | .fml f => Formula.to_tptp f

  partial def Formula.to_tptp : Formula -> String
    | Formula.not f => s!"~({Formula.to_tptp f})"
    | Formula.and a b => s!"({Formula.to_tptp a} & {Formula.to_tptp b})"
    | Formula.or a b => s!"({Formula.to_tptp a} | {Formula.to_tptp b})"
    | Formula.implies a b => s!"({Formula.to_tptp a} => {Formula.to_tptp b})"
    | Formula.lit b => ToTPTP.to_tptp b
    | Formula.eq a b => s!"({Formula.to_tptp a} = {Formula.to_tptp b})"
    | Formula.qforall name type body =>
        if let some type := type then
          s!"(![{name} : {Typ.to_tptp type}]: {Formula.to_tptp body})"
        else
          s!"(![{name}]: {Formula.to_tptp body})"
    | Formula.exists name type body =>
        if let some type := type then
          s!"(?[{name} : {ToTPTP.to_tptp type}]: {Formula.to_tptp body})"
        else
          s!"(?[{name}]: {Formula.to_tptp body})"
    | Formula.const c => c
    | Formula.var c => c
    | Formula.app f arg => s!"({Formula.to_tptp f} @ {Formula.to_tptp arg})"
    | Formula.term arg => Term.to_tptp arg
end

instance: ToTPTP Term where
  to_tptp: Term -> String := Term.to_tptp

instance: ToTPTP Formula where
  to_tptp: Formula -> String := Formula.to_tptp

/-- Annotated formula, for example `thf(name, axiom, ...).`. -/
inductive Item where
| ax (id : String) (formula : Formula) : Item
| conjecture (id : String) (formula : Formula) : Item
| typeDecl (id : String) (symbol : String) (typ : Typ) : Item
| comment (str : String) : Item
deriving Repr

instance: ToTPTP Item where
  to_tptp : Item -> String
    | Item.ax id formula => s!"thf({id}, axiom, {to_tptp formula})."
    | Item.conjecture id formula => s!"thf({id}, conjecture, {to_tptp formula})."
    | Item.typeDecl id symbol typ => s!"thf({id}, type, {symbol} : {to_tptp typ})."
    | Item.comment str => s!"% {str}"

def TPTPFile := List Item

instance: ToTPTP <| List Item where
  to_tptp (file: TPTPFile) : String :=
    file.foldr
      (fun item acc => acc ++ (to_tptp item) ++ "\n")
      ""

end Data

inductive NameRole | Variable | Global

/--
  Encode a name into some (hopefully) globally unique string which is accepted by TPTP.
  This is a little janky, but works for now.
-/ 
def mangleString (s: String) (role: NameRole := NameRole.Global) : String :=
  let s := s.toList.map f |>.foldr (fun str acc => str ++ acc) ""
  -- TPTP global constants must start with a lowercase letter.
  -- TPTP variables (i.e. bound to a binder) must start with an uppercase letter.

  match role with
  | NameRole.Variable => s!"VAR_{s}"
  | NameRole.Global => s!"glob_{s}"
  -- let head := s.get! 0
  -- let tail := s.drop 1
  -- match role, head.isUpper, head.isAlpha with
  -- | NameRole.Variable, false, false => s!"VAR_{s}"
  -- | NameRole.Global, true, false => s!"global_{s}"
  -- | NameRole.Variable, false, true => s!"{head.toUpper}{tail}"
  -- | NameRole.Global, true, true => s!"{head.toLower}{tail}"
  -- | _, _, _ => s
where f: Char -> String
  | '.' => "_"
  | '@' => "_"
  | '«' => ""
  | '»' => ""
  | '\'' => "_prime"
  | '!' => "EXCL"
  | '?' => "QUEST"
  | 'α' => "alpha"
  | 'β' => "beta"
  | 'γ' => "gamma"
  | 'τ' => "tau"
  | 'σ' => "sigma"
  | 'π' => "pi"
  | '∏' => "PI"
  | 'Σ' => "SIGMA"
  | 'Γ' => "GAMMA"
  | 'ℕ' => "BLACKBOARDBOLD_N"
  | 'ℝ' => "BLACKBOARDBOLD_R"
  | '𝔹' => "BLACKBOARDBOLD_B"
  | '₁' => "_sub1"
  | '₂' => "_sub2"
  | '₃' => "_sub3"
  | '¹' => "_pow1"
  | '²' => "_pow2"
  | '³' => "_pow3"
  | c => 
    if c.isAlphanum || c == '_' then s!"{c}"
    else s!"UNICODE{c.toNat}"

#eval mangleString "α₂"
#eval mangleString "hello@α"
#eval mangleString "s"
#eval mangleString "%"

/--
  Encode a name into some (hopefully) globally unique string which is accepted by TPTP.
  This is a little janky, but works for now.
-/ 
def mangleName [Monad m] [MonadError m] (n: Name) (role: NameRole := NameRole.Global) : m String :=
  return mangleString s!"{n}" role

structure State where
  axiomCounter : Nat := 0
  nameAlloc : HashMap Name String := HashMap.empty
    -- Hacky
    |>.insert ``Bool "$o"
    |>.insert ``true "$true"
    |>.insert ``false "$false"
  
  equations : HashMap Name (HashSet Name)
  
  /-- Lean4 consts (from Environment) which have been encoded, or are in the process of being encoded. -/
  visitedBegun     : HashSet Name := {}
  /-- Lean4 consts (from Environment) which have been encoded.
    If a name is in `visitedCompleted`, it must already approprietely encoded in `items`.
  -/
  visitedCompleted : HashSet Name := {}

  /-- TPTP Items in order. -/
  items : List Item := []
deriving Inhabited

abbrev BinderStack := List LocalDecl
abbrev EncodeM := ReaderT BinderStack (StateRefT State TermElabM)

private def EncodeM.nextCounter : EncodeM Nat := do
  let state <- get
  set {state with axiomCounter := state.axiomCounter + 1}
  return state.axiomCounter

def EncodeM.name2string (n : Name) (role : NameRole := NameRole.Global): EncodeM String := do
  let state : State <- get
  if let some s := state.nameAlloc.find? n then
    return s
  else
    let s <- mangleName n role
    let x := state.nameAlloc.insert n s
    set { state with nameAlloc := x }
    return s

private def EncodeM.mangleFVar (ldecl : LocalDecl) : EncodeM String := do
  if (<- read).any fun decl => decl.fvarId == ldecl.fvarId then
    -- This FVar has been introduced via a `Meta.forallBoundedTelescope` (or `EncodeM.visitForall`).
    -- So it originates from a `(x : τ) -> ...` binder, and needs to be encoded with initial uppercase.
    -- Also, TPTP allows shadowing of binders, so we don't need to worry about name collisions.
    mangleName s!"{ldecl.userName}" NameRole.Variable
  else
    -- We use NameRole.Global, since even though it's the localContext, we just model localDecls
    -- with global constant definitions.
    return mangleString s!"local_{ldecl.userName}_{ldecl.toExpr}" NameRole.Global

/-- Creates a new fvar accordingly and calls `m` on it.
  Also pushes that fvar onto the BinderStack and pops it when leaving. -/
private def EncodeM.visitForall (e : Expr) (m : LocalDecl -> Expr -> EncodeM α): EncodeM α := do
  let .forallE varName dom body bi := e
    | throwError "EncodeM.visitForall: Expected a forall, but it is not: {e}"
  let varName :=
    if ((<- getLCtx).findFromUserName? varName).isNone then varName
    else varName ++ (<- mkFreshId)
  Meta.forallBoundedTelescope (.forallE varName dom body bi) (some 1) fun var body => do
    let decl <- Meta.getFVarLocalDecl var[0]!
    if (<- read).any fun d => d.userName == decl.userName then
      throwError "oh no"
    withReader (fun stack => decl :: stack) do
      m decl body

/-- Creates a new fvar accordingly and calls `m` on it.
  Also pushes that fvar onto the BinderStack and pops it when leaving. -/
private def EncodeM.visitLambda (e : Expr) (m : LocalDecl -> Expr -> EncodeM α): EncodeM α := do
  let .lam var dom body bi := e
    | throwError "EncodeM.visitLambda: Expected a Lambda, but it is not: {e}"

  let var :=
    if ((<- getLCtx).findFromUserName? var).isNone then var
    else var ++ (<- mkFreshId)

  let fvarId <- mkFreshFVarId
  let body := body.instantiate1 (.fvar fvarId) -- replace the now-loose bvar with our fvar
  let lctx := (<- getLCtx).mkLocalDecl fvarId var dom bi
  withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) do
    let decl := lctx.get! fvarId
    if (<- read).any fun d => d.userName == decl.userName then
      throwError "oh no"
    withReader (fun stack => decl :: stack) do
      m decl body

private def EncodeM.appendItem (item : Item) : EncodeM Unit := do
  trace[HoSmt.Encoding.appendItem] "{repr item}"
  let state <- get
  set {state with items := item :: state.items}
  
private def EncodeM.comment (msg : String) : EncodeM Unit := do
  appendItem <| Item.comment msg

/--
  Only obtain a Subtype's data component, getting rid of the proposition.

  - Given an expression `{ val : T // P val }`, return just `T`.
  - Given an expression `@Subtype.mk T P val prf`, return just `val`.

  Note that `val : T`.
-/
private def viewSubtypeData (expr : Expr) : TermElabM Expr := do
  -- let .const fn _ := expr.getAppFn | throwError "viewSubtypeData {expr} is not an app of const"
  if expr.isAppOf ``Subtype then
    let args := expr.getAppArgs
    if h : 0 < args.size then 
      return args[0]
    else throwError "viewSubtypeData: Not enough args to Subtype"
  else if expr.isAppOf ``Subtype.mk then
    let args := expr.getAppArgs
    if h : 2 < args.size then
      return args[2]
    else throwError "viewSubtypeData: No enough args to Subtype.mk"
  else
    return expr
    -- throwError "viewSubtypeData: Not a app of Subtype or Subtype.mk, instead is a {expr}"

private def logTraverse [ToMessageData α] [ToMessageData β] (note : MessageData) (input : β) : Except ε α -> EncodeM MessageData
| .ok val => return m!"{note} {input} ~~> {val}"
| .error _ => return m!"{note} {input} ~~> error"

mutual

private partial def encodeType (expr : Expr) : EncodeM Typ := do
  withTraceNode `HoSmt.Encoding.traverse (logTraverse "encodeType" expr) do
    let expr <- viewSubtypeData expr
    match expr with
    | .mdata _ inner => encodeType inner
    | .const name _ => return Typ.SCustom (<- EncodeM.name2string name NameRole.Global)
    | .forallE _ dom body _ => do
      let domType <- Meta.inferType dom
      let isDependent := body.hasLooseBVars
      match isDependent, domType.isProp with
      | false, false => return Typ.SAbstr (<- encodeType dom) (<- encodeType body) -- α -> β
      | false, true  =>
        -- TODO: generate pre/postconditions from the prop:
        encodeType body -- skip prop
      | true, false  => do
        -- When we're encoding `VectInv` (from index erasure), its ctors have dependent type arrows.
        -- For example `(v : Vect') -> VectInv n v -> ...` (remember Subtype doesn't work inside TInv...).
        -- However, only propositions depend on those binders, so it should be fine.
        EncodeM.visitForall expr fun _decl body => do
          return Typ.SAbstr (<- encodeType dom) (<- encodeType body)
          -- throwError "While encoding type {expr}, still have dependent arrows."
      | true, true   => do
        -- For some reason have `(prf : n = 5) -> body` with `prf` actually used in body? weird.
        EncodeM.visitForall expr fun _decl body => do
          -- Just hope the fvar somehow makes sense later, I guess.
          -- TODO: generate pre/postconditions from the prop:
          encodeType body -- skip the prop.
    | .sort .zero => return Typ.SBool
    | _ => throwError "Don't know how to encode type {expr} to TPTP"

private partial def encodeTerm (expr: Expr): EncodeM Term := do
  if (<- Meta.inferType expr).isProp then
    -- throwError "TODO: Formulas inside terms"
    return Term.fml <| <- encodeFormula expr

  withTraceNode `HoSmt.Encoding.traverse (logTraverse "encodeTerm" expr) do
    let expr <- viewSubtypeData expr
    if (<- Meta.inferType (<- Meta.inferType expr)).isProp then
      throwError "encodeTerm: Can't encode proofs (prf : ... : Prop) into terms. It should never come to this in the first place, this is a bug. Expr is {expr}"
    if let .app fn arg := expr then do
      if (<- Meta.inferType (<- Meta.inferType arg)).isProp then
        -- skip proofs passsed as arguments.
        encodeTerm fn
      else
        return Term.app (<- encodeTerm fn) (<- encodeTerm arg)
    else if let some name := expr.constName? then
      return Term.const <| <- EncodeM.name2string name
    else if let Expr.fvar id := expr then
      let fvar : LocalDecl <- id.getDecl
      let tmp <- EncodeM.mangleFVar fvar
      return Term.const tmp
    else if let .lam _ dom _ _ := expr then
      let domType <- Meta.inferType dom
      EncodeM.visitLambda expr fun decl body => do
        if domType.isProp then
          -- skip prop binder `λprf : n = 5, ...`
          encodeTerm body
        else
          return Term.abstr
            (<- EncodeM.mangleFVar decl)
            (<- encodeType dom)
            (<- encodeTerm body)
    else if let .proj T idx obj := expr then
      if (``Subtype).isPrefixOf T && idx == 0 then
        return <- encodeTerm obj

      -- Replace for example `pair.1` with `Prod.fst pair`
      let some structInfo := Lean.getStructureInfo? (<- getEnv) T | throwError "{T} has no structureInfo but projection functions?"
      let some projFn := structInfo.getProjFn? idx | throwError "{T} has no projFn for idx = {idx}"
      let expr' <- Meta.mkAppM projFn #[obj] -- hope this infers the levels correctly..

      trace[HoSmt.Encoding.traverse] "Replacing projection {repr expr} with {repr expr'}"
      encodeTerm expr'
    else if let .lit (.natVal n) := expr then
      let rec tf
      | Nat.zero => Expr.const ``Nat.zero []
      | Nat.succ k => Expr.app (.const ``Nat.succ []) (tf k)
      let expr' := tf n
      encodeTerm expr'
    else
      throwError "Don't know how to encode {expr} ({expr.ctorName})"

private partial def encodeFormula (expr: Expr) : EncodeM Formula := do
  withTraceNode `HoSmt.Encoding.traverse (logTraverse "encodeFormula" expr) do
    -- let expr <- viewSubtypeData expr
    if !(<- Meta.inferType expr).isProp then
      return Formula.term (<- encodeTerm expr)
    match expr with
    | .const ``True _ => return Formula.lit True
    | .const ``False _ => return Formula.lit False
    | .const name _ => return Formula.const <| <- mangleName name
    | .app lhs rhs => do
      if let some (a, b) := expr.eqOrIff? then
        -- if a and/or b are Prop, will encode as formula, otherwise will encode as term.
        return Formula.eq (<- encodeFormula a) (<- encodeFormula b)
      if let some (_α, a, _β, b) := expr.app4? ``HEq then
        -- Heterogenous equality. For now just hope α = β...
        return Formula.eq (<- encodeFormula a) (<- encodeFormula b)
      else if let some (a, b) := expr.and? then
        return Formula.and (<- encodeFormula a) (<- encodeFormula b)
      else if let some (a, b) := (expr.app2? ``Or) then
        return Formula.or (<- encodeFormula a) (<- encodeFormula b)
      else if let some a := expr.not? then
        return Formula.not (<- encodeFormula a)
      else if let some (_dom, lam) := expr.app2? ``Exists then
        let .lam var dom body bi := <- (Meta.withReducible <| Meta.whnf lam) | throwError "Exists without body being a lambda: {expr}"
        let dom' <- encodeType dom
        let var :=
          if ((<- getLCtx).findFromUserName? var).isNone then var
          else var ++ (<- mkFreshId)
        let fvarId <- mkFreshFVarId
        let body := body.instantiate1 (.fvar fvarId)
        let lctx := (<- getLCtx).mkLocalDecl fvarId var dom bi
        let tmp <- withTheReader Meta.Context (fun ctx => { ctx with lctx := lctx }) do
          let decl := lctx.get! fvarId
          withReader (fun stack => decl :: stack) do
            -- Now we have entered the `∃` "binder".
            let body' <- encodeFormula body
            return Formula.exists (<- EncodeM.mangleFVar decl) dom' body'
        return tmp
      else
        -- let rhsF <- if (<- Meta.inferType rhs).isProp then encodeFormula rhs
        --   else Formula.term
        return Formula.app (<- encodeFormula lhs) (<- encodeFormula rhs)
    | .forallE _ dom body _ => do
      let domType <- Meta.inferType dom
      let isDependent := body.hasLooseBVars
      match isDependent, domType.isProp with
      | false, true =>
        -- Just normal implication: α -> β
        return Formula.implies (<- encodeFormula dom) (<- encodeFormula body)
      | true, true   => do
        -- For some reason have `∀prf : n = 5, body` with `prf` actually used in body? weird.
        -- This *should* be just an implication, as both domain and body are propositions...
        -- Need to use visitForall anyway since we can't just have loose bvars.
        EncodeM.visitForall expr fun _decl body => do
          -- Just hope the fvar somehow makes sense later, I guess.
          return Formula.implies (<- encodeFormula dom) (<- encodeFormula body)
      | _, false => do
        -- Either `∀x : Nat, x = 4` (dependent)
        -- or     `∀_ : Nat, 1 = 2` (non-dependent)
        let dom' := <- encodeType dom
        EncodeM.visitForall expr fun decl body => do
          -- We have pushed _decl onto the binderstack, so this encodeFormula will know
          -- to encode a LocalDecl resulting from `(n : Nat) -> ...` as `N` and not as `n`:
          let newbody <- encodeFormula body
          return Formula.qforall (<- EncodeM.mangleFVar decl) dom' newbody
    | .fvar id => do
      let ldecl <- id.getDecl
      return Formula.var (<- EncodeM.mangleFVar ldecl)
    | _ => throwError "Don't know how to encodeFormula[{expr.ctorName}] {expr}"

end

/--
Given   `{α : Type} -> {β : Type} -> (a:α) -> (b:β) ->     Prod α β`
Produce `{α : Type} -> {β : Type} -> (a:α) -> (b:β) -> p : Prod α β -> p = mk {α β} a b -> fst p = a`
-/
private def mkProjFnEqn (projFn : Name) : EncodeM Expr := do
  -- withTraceNode `HoSmt.Encoding (fun res => do return match res with | .ok ret => m!"Encoded proj fn {projFn} into equation {ret}" | _ => m!"argh") do
  withTraceNode `HoSmt.Encoding.traverse (logTraverse "mkProjFnEqn" projFn) do
    let env <- getEnv
    let some projFnInfo <- Lean.getProjectionFnInfo? projFn | throwError "{projFn} is not a projection function"
    let some structName := env.getProjectionStructureName? projFn | throwError "{projFn} is not a projection function"
    let some (.inductInfo structInductInfo) := env.find? structName | throwError "no induct {structName} in env"
    assert! structInductInfo.numIndices == 0

    let mk := projFnInfo.ctorName -- Prod.mk
    let some (.ctorInfo mk_ci) := env.find? mk | throwError "no {mk} in env"

    -- Given   `{α : Type} -> {β : Type} -> (a:α) -> (b:β) ->     Prod α β`
    --          ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ (params)
    --                                                        ^^^^^^^^^^^^ (target)
    -- Produce `{α : Type} -> {β : Type} -> (a:α) -> (b:β) -> p : Prod α β -> p = mk {α β} a b -> fst p = a`
    Util.visitManyForall mk_ci.type none fun params target_type => do
      -- body is now the `α` all the way on the right.
      Meta.withLocalDeclD `target target_type fun target_fv => do
        -- p = mk {α β} a b
        let target_eq_mkargs : Expr := mkApp3 (mkConst ``Eq [<- Meta.mkFreshLevelMVar]) target_type
          target_fv
          (mkAppN (mkConst mk_ci.name (structInductInfo.levelParams.map Level.param)) params)
        
        let body₁ <- Meta.withLocalDeclD `target_eq_mkargs target_eq_mkargs fun fv₂ => do
          -- Util.debugLocalContext "[3]"
          let field_fv := params[mk_ci.numParams + projFnInfo.i]! -- `a` or `b` (i-th struct field)
          let field_type <- field_fv.fvarId!.getType -- for field `a`, this is `α`
          -- `fst α β target = a`
          let body₂ : Expr := mkApp3 (mkConst ``Eq [<- Meta.mkFreshLevelMVar]) field_type
            (mkAppN -- fst {α β} target
              (mkConst projFn (structInductInfo.levelParams.map Level.param))
              (params[:mk_ci.numParams].toArray ++ #[target_fv]))
            field_fv
          Meta.mkForallFVars #[fv₂] body₂
        Meta.mkForallFVars #[target_fv] body₁

/-- The only difference between defs and theorems in Lean is code gen, which for us is wurst. -/
private def encodeDefnOrThm (name : Name) (levels : List Name) (type : Expr) (value : Expr) : EncodeM Unit := do
  if (<- Meta.inferType type).isProp then
    -- Theorem
    EncodeM.comment s!"axiom {name} : {type}"
    EncodeM.appendItem <| Item.ax
      s!"ax{<- EncodeM.nextCounter}"
      (<- encodeFormula type)
    return

  -- Function (... -> α) or predicate (... -> Prop)
  EncodeM.comment s!"{name} : {type}"
  EncodeM.appendItem <| Item.typeDecl
    s!"ty{<- EncodeM.nextCounter}"
    (<- EncodeM.name2string name)
    (<- encodeType type)

  if <- Lean.isProjectionFn name then
    -- We want to encode projection functions in a special way.
    let eq <- mkProjFnEqn name
    EncodeM.comment s!"ProjFn def {name}"
    EncodeM.appendItem <| Item.ax
      s!"ax{<- EncodeM.nextCounter}"
      (<- encodeFormula eq)
    return

  if value.getUsedConstants.contains ``sorryAx then
    -- We already encoded the type, and can't encode the body. Nothing else to do.
    return

  -- Reminder: `getEqnsFor _ false` does not create equations for non-recursive defns.
  let eqns <- Meta.getEqnsFor? name false
  if let some eqns := eqns then
    -- Have recursive defn, so it contains recusors. Thus can't encode via lambda value,
    -- and we need the equations.
    for eq in eqns do
      let some (ConstantInfo.thmInfo ci) := (<- getEnv).find? eq | throwError "no such theorem {eq}"
      trace[HoSmt.Encoding.defEqns] m!"Equation {eq}\n::: {ci.type}"
      EncodeM.comment s!"theorem {eq} : {ci.type}"
      EncodeM.appendItem <| Item.ax
        s!"ax{<- EncodeM.nextCounter}"
        (<- encodeFormula ci.type)
  else
    -- Non-recursive defn, can encode directly: `f = value`
    -- (where value is a lambda-telescope)
    let eq : Expr := mkApp3
      (.const ``Eq [<- Meta.mkFreshLevelMVar])
      (<- Meta.inferType value)
      (.const name (levels.map Level.param))
      value
    trace[HoSmt.Encoding.defEqns] "Our own self-generated eq is {eq}"
    EncodeM.comment s!"def(lambda) {name} === {value}" -- TODO: not so sure about this...
    EncodeM.appendItem <| Item.ax
      s!"ax{<- EncodeM.nextCounter}"
      (<- encodeFormula eq)

/--
  Given for example
  ```
  inductive VecInv : Vec' -> Nat -> Prop where
  | invNil             :                                  VecInv (Vec'.nil)         0
  | invCons {v : Vec'} : (elem : String) -> VecInv v n -> VecInv (Vec'.cons elem v) (Nat.succ n)
  ```

  We want to produce the following, translating `Prop` as the boolean type `$o`.
  ```tptp
  thf(type, vecInv : vec' > nat > $o). % the type of Vec'Inv itself
  thf(ax,   vecInv @ vec'.nil @ nat.zero). % invNil
  thf(ax,   ...). % invCons
  ```
-/
private def encodeInductivePredicate (P : InductiveVal) : EncodeM Unit := do
  withTraceNode `HoSmt.Encoding (fun _ => return m!"Encoding inductive predicate {P.name}") do
    -- Translate `P : Vec -> Nat -> Prop`
    let ty <- encodeType P.type
    let s <- EncodeM.name2string P.name
    EncodeM.comment s!"inductive predicate {P.name} : {P.type}"
    EncodeM.appendItem <| Item.typeDecl s!"ty{<- EncodeM.nextCounter}" s ty
    
    -- Translate each ctor as axiom
    for ctor in P.ctors do
      -- let s <- EncodeM.name2string ctor
      let ctorInfo <- HoSmt.Util.TermElabM.getCtor! ctor
      let frm <- encodeFormula ctorInfo.type
      EncodeM.comment s!"inductive predicate ctor {ctor} : {ctorInfo.type}"
      EncodeM.appendItem <| Item.ax s!"ax{<- EncodeM.nextCounter}" frm

    -- TODO: translate recursor?

/--
  We only permit simple types with no type params or indices.
-/
private def encodeInductiveType (T : InductiveVal) : EncodeM Unit := do
  withTraceNode `HoSmt.Encoding (fun _ => return m!"Encoding inductive type {T.name}") do
    if T.numParams != 0 || T.numIndices != 0 then
      throwError "{T.name}: Only simple inductive types can be encoded"
    
    withTraceNode `HoSmt.Encoding (fun _ => return m!"Encoding {T.name} : {T.type}") do
      -- Since T is a simple type, it necessarily is like `T : Type` and that's it.
      let name <- EncodeM.name2string T.name
      EncodeM.comment s!"inductive {T.name} : {T.type}"
      EncodeM.appendItem <| Item.typeDecl s!"ty{<- EncodeM.nextCounter}" name Typ.SType

    for ctor in T.ctors do
      let ctorInfo <- HoSmt.Util.TermElabM.getCtor! ctor
      withTraceNode `HoSmt.Encoding (fun _ => return m!"Encoding {ctor} : {ctorInfo.type}") do
        let ty <- encodeType ctorInfo.type
        let name <- EncodeM.name2string ctorInfo.name
        let item := Item.typeDecl s!"ty{<- EncodeM.nextCounter}" name ty
        EncodeM.comment s!"ctor {ctor} : {ctorInfo.type}"
        EncodeM.appendItem item

      -- if let some <| .thmInfo injThm := (<- getEnv).find? <| Lean.Meta.mkInjectiveTheoremNameFor ctor then
      --   withTraceNode `HoSmt.Encoding.inj (fun _ => return m!"Encoding {injThm.name} : {injThm.type}") do
      --     encodeDefnOrThm injThm.name injThm.levelParams injThm.type injThm.value
      -- else trace[HoSmt.Encoding.inj] "Can't find inj theorem for ctor {ctor}"

      -- inj follows from injEq
      if let some <| .thmInfo injEqThm := (<- getEnv).find? <| Lean.Meta.mkInjectiveEqTheoremNameFor ctor then
        withTraceNode `HoSmt.Encoding.inj (fun _ => return m!"Encoding {injEqThm.name} : {injEqThm.type}") do
          encodeDefnOrThm injEqThm.name injEqThm.levelParams injEqThm.type injEqThm.value
      else trace[HoSmt.Encoding.inj] "WARN: Can't find injEq theorem for ctor {ctor}"

/-- Encode an item from the environment, such as a type, function definition, axiom, etc. -/
private def encodeEnvironment (name: Name) : EncodeM Unit := do
  let env <- getEnv
  let some info := env.find? name
    | throwError "[TPTP.encEnv] No such symbol in environment: {name}"

  match info with
  | ConstantInfo.inductInfo info => do
    -- If we have `inductive: ... -> Prop`, then encode as inductive predicate.
    if <- Util.isInductivePredicate info then
      encodeInductivePredicate info
    else
      encodeInductiveType info

  | ConstantInfo.axiomInfo info => 
    let tyty <- Meta.inferType info.type
    if info.type.isType then
      -- `axiom ax : Type u`
      EncodeM.appendItem <| Item.typeDecl
        s!"ty{<- EncodeM.nextCounter}"
        (<- EncodeM.name2string info.name)
        Typ.SType
    else if tyty.isProp then
      -- `axiom ax : 1 = 2 ::: Prop`
      EncodeM.appendItem <| Item.ax
        s!"ax{<- EncodeM.nextCounter}"
        (<- encodeFormula info.type)
    else if tyty.isType then
      EncodeM.appendItem <| Item.typeDecl
        s!"ty{<- EncodeM.nextCounter}"
        (<- EncodeM.name2string info.name)
        (<- encodeType info.type)
    else
      throwError "Don't know how to encode axioms such as {info.name} : {info.type}"

  | ConstantInfo.defnInfo info => encodeDefnOrThm info.name info.levelParams info.type info.value
  | ConstantInfo.thmInfo  info => encodeDefnOrThm info.name info.levelParams info.type info.value
  | ConstantInfo.ctorInfo _ => throwError "TPTP.encodeEnvironment: Ctors should not be encodeEnvironmented, but rather go via encodeInductive* stuff."
  | _ => throwError f!"Encoding environment items like {info.name} is not yet implemented"
  
/-- Encode an axiom passed explicitly by the user, or from LocalContext (`have`, ...), which
  doesn't exist in the environment.
-/
private def encodeLocal (decl : LocalDecl) : EncodeM Unit := do
  let ctr <- EncodeM.nextCounter
  
  if (<- Meta.inferType decl.type).isProp then
    EncodeM.appendItem <| Item.ax s!"ax{ctr}" (<- encodeFormula decl.type)
  else if decl.type.isType then
    let item := Item.typeDecl
      s!"ty{ctr}"
      (<- EncodeM.mangleFVar decl) -- this will encode as `fvar_local_....` because this fvar is not in EncodeM's BinderStack.
      (<- encodeType decl.type)
    EncodeM.appendItem item
  else
    throwError "Don't know how to encode local context decl[kind={repr decl.kind} name={decl.userName}] {decl.type}"

/-- Encode the main conjecture. -/
private def encodeGoal (expr: Expr) : EncodeM Unit := do
  let item := Item.conjecture "goal" (<- encodeFormula expr)
  EncodeM.appendItem item

def EncodeM.run (equations : HashMap Name (HashSet Name) := {}) (m : EncodeM Unit) : TermElabM String := do
  let ((), (state : State)) <- StateRefT'.run (ReaderT.run m []) { equations := equations }
  return ToTPTP.to_tptp state.items

def EncodeM.visitBegin (name : Name) : EncodeM Unit :=
  modify fun s => { s with visitedBegun := s.visitedBegun.insert name }
def EncodeM.visitEnd (name : Name) : EncodeM Unit :=
  modify fun s => { s with visitedCompleted := s.visitedCompleted.insert name }
def EncodeM.isCompleted (name : Name) : EncodeM Bool := do
  return (<- get).visitedCompleted.contains name

/-- Append a const to the TPTP file.
  Also adds any not-yet-added dependencies of `name`.
  Also adds any equations of `name`, such as equations for `List.map`, which need to be appended
  after `name`.
-/
partial def addConst (name : Name) : EncodeM Unit :=
  go [] name
where
  /-- Stack is just for debugging. -/
  go (stack : List Name) (name : Name)  : EncodeM Unit := do
    if primitives.contains name then return
    if <- EncodeM.isCompleted name then return -- already visited
    -- TODO: if name is in visitedBegun but not visitedCompleted, that means we have a cycle? Tho the `stack` already catches those cases.

    let some ci := (<- getEnv).find? name | throwError "no such const {name}"
    if let .ctorInfo ctorInfo := ci then
      -- Just pretend we were called with the inductive type instead.
      go stack ctorInfo.induct
      return

    if stack.contains name then
      throwError "[TPTP.addConst {name}] Found a cyclic dependency, stack is {stack}"

    EncodeM.visitBegin name
    let deps <- HoSmt.Util.ConstantInfo.getUsedConstantsClean ci {}
    let log
    | .ok () => return m!"addConst {name} with deps {deps}"
    | .error _ => return m!"addConst {name} with deps {deps}"
    withTraceNode `HoSmt.Encoding.traverse log do
      -- trace[HoSmt.debug] "{name} has deps {deps}"

      -- Make sure all deps have been encoded.
      deps.forM <| go (name :: stack)

      -- Encode this const
      encodeEnvironment name
      EncodeM.visitEnd name

      -- Handle projection functions (as if they were in equations)
      if let some si := Lean.getStructureInfo? (<- getEnv) name then
        [0 : si.fieldNames.size].forM fun idx => do
          addConst <| si.getProjFn? idx |>.get!

      -- Encode equations (e.g. if name is `List.map`, then map's equations might be equations)
      let equations := (<- get).equations.findD name {}
      trace[HoSmt.debug] "addConst {name} has equations {equations}"
      equations.forM <| go (name :: stack)

def addGoal (goal : MVarId) : EncodeM Unit := do
  goal.withContext do
    let decl <- goal.getDecl
    let deps <- HoSmt.Util.getUsedConstantsWithProj decl.type
    deps.forM addConst
    encodeGoal decl.type

end TPTP