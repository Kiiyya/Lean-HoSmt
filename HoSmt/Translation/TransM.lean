import Lean
import Lean.Data
import HoSmt.Util

open Lean Elab Term Command Tactic Expr Std
open HoSmt.Util

namespace HoSmt.Translation

/-!
  The translation monad with translation state.
  Maybe an environment extension would be better, so that we won't need to spin
  our own monad at all.
-/

instance : ToMessageData <| HashMap Name Name where
  toMessageData map := (map.fold (fun acc key val => m!"{acc}{key} ↦ {val}, ") "{") ++ "}"

inductive MonomorphizedInfo where
| induct
  /- If T was `List`, this will be `List_Nat` -/
  (name : Name)
  /- For example `List.nil` to `List_Nat.nil` -/
  (ctors : HashMap Name Name)
| defn (name : Name)

def MonomorphizedInfo.defn! : MonomorphizedInfo -> Name
| .induct .. => panic! "Not a MonomorphizedInfo.defn :("
| .defn name => name

instance: ToMessageData <| MonomorphizedInfo where
  toMessageData
  | .induct name ctors => m!"MonomorphizedInfo.induct {name} {ctors}"
  | .defn name => m!"MonomorphizedInfo.defn {name}"

/-- Type index erasure info. -/
inductive IndexErasureInfo where
| notNecessary : IndexErasureInfo
| erased (erased guard : Name) (pattern : List Bool) (nRemovedParams : Nat) : IndexErasureInfo
deriving Repr, BEq, Inhabited

inductive MonoTraversal where
| notNecessary : MonoTraversal
| mono : Name -> MonoTraversal
deriving Repr, BEq, Inhabited

def MonoTraversal.getD (default : Name) : MonoTraversal -> Name
| .notNecessary => default
| .mono n => n

inductive IndexErasureTraversalInfo where
| notNecessary : IndexErasureTraversalInfo
| changed : (const' : Name) -> (uniqSuffix : Option Name := none) -> IndexErasureTraversalInfo
deriving Repr, BEq, Inhabited

def IndexErasureTraversalInfo.getD (default : Name) : IndexErasureTraversalInfo -> Name
| .notNecessary => default
| .changed n _ => n

structure TransS where
  /-- Mapping of polymorphic types to their concrete monomorphized variants.
    For example `(List, #[Expr.const Nat]) => List_Nat`.
    For example `(someFunc, #[Expr.lit 42]) => List_Nat`.
    If an arg is `none`, then it is not monomorphized.
  -/
  monoMapArgs : HashMap Name (HashMap (Array (Option Expr)) MonomorphizedInfo) := {}

  /-- Mapping of env items to their monomorphized variants.
    If a defn doesn't have polymorphic binders (`(α:Type)->...`) in its type, it can still contain
    occurences of polymorphic types (such as `List Nat`) in its type and/or value,
    which need to be replaced by their monomorphic variants.

    A mapping of `myfunc => none` means that `myfunc` has been checked and does not contain
    references to polymorphic types anymore, so it doesn't need to be replaced.
  -/
  monoMapGeneral : HashMap Name MonoTraversal := {}

  /--
    These are kind of "explicit dependencies", but are encoded after the env item, not before.
    For example when we have `List.map` whose body can't be translated, and instead we generate
    equations with which our translation then continues instead.

    Example entry: `map ↦ {map.eq1, map.eq2}`.
    When `map` gets translated, we add a new entry
    `map.42 ↦ {map.eq1.42, map.eq2.42}`.
  -/
  equations : HashMap Name (HashSet Name) := {}

  /-- Mapping of for example `Vec` to `(VecE, VecG)` -/
  indexErasure : HashMap Name IndexErasureInfo := {}

  indexErasureTraversal : HashMap Name IndexErasureTraversalInfo := {}

  /-- Just a lil' debugging helper, to prevent stack overflows. -/
  depth : Nat := 0

abbrev TransM := StateRefT TransS TacticM

def registerMonoGeneral (original : Name) (info : MonoTraversal) : TransM Unit := do
  modify fun s => {s with monoMapGeneral := s.monoMapGeneral.insert original info}

def registerMonoOfArgs (original : Name) (args : Array (Option Expr)) (info : MonomorphizedInfo) : TransM Unit := do
  modify fun s =>
    let updatedVariants := s.monoMapArgs.findD original {} |>.insert args info
    { s with monoMapArgs := s.monoMapArgs.insert original updatedVariants }

def checkXEcache (T : Name) : TransM (Option IndexErasureInfo) := do
  return (<- get).indexErasure.find? T

def registerXEcache (T : Name) (info : IndexErasureInfo) : TransM Unit := do
  modify fun s => { s with indexErasure := s.indexErasure.insert T info }

def checkXETcache (T : Name) : TransM (Option IndexErasureTraversalInfo) := do
  return (<- get).indexErasureTraversal.find? T

def registerXETcache (T : Name) (info : IndexErasureTraversalInfo) : TransM Unit := do
  modify fun s => { s with indexErasureTraversal := s.indexErasureTraversal.insert T info }

def registerEquations [ForIn Id ρ Name] (src : Name) (equations : Option ρ) : TransM Unit := do
  let some equations := equations | return
  modify fun s =>
    let deps' := s.equations.findD src {} |>.insertMany equations
    { s with equations := s.equations.insert src deps' }
def registerExtra (src : Name) (extra : Name) : TransM Unit := do
  modify fun s =>
    let deps' := s.equations.findD src {} |>.insert extra
    { s with equations := s.equations.insert src deps' }
def removeequations (src : Name) (equations : Array Name) : TransM Unit := do
  modify fun s =>
    if let some oldequations := s.equations.find? src then
      let res := equations.foldl (fun acc toRemove => acc.erase toRemove) oldequations
      if res.isEmpty then { s with equations := s.equations.erase src }
      else { s with equations := s.equations.insert src res }
    else s
def replaceEquations (src : Name) (old : Array Name) (new : Option <| Array Name) : TransM Unit := do
  removeequations src old
  registerEquations src new

/-- Ensure that the definition has its equations (only if recursive) in `equations`. -/
def ensureHasEqns (name : Name) : TransM Unit := do
  if let some _equations := (<- get).equations.find? name then
    -- Already have equations for this item.
    return
  else
    if name == ``ite then
      -- getEqnsFor ite just gives us `none`.
      registerEquations ``ite (some [``ite_true, ``ite_false])

    -- We don't force generation of equations (only functions with pattern matching need mulitple eqns).
    if let some eqns := <- Meta.getEqnsFor? name false then
      registerEquations name (some eqns)
    -- Uncomment for logging:
    -- for eq in eqns do
    --   let some eqCi := (<- getEnv).find? eq | throwError "no such eqn {eq}"
    --   trace[HoSmt.Translation.sry] "theorem {eq} : {eqCi.type}"

/--
  Little debugging tool to prevent hard stack overflows, and to still print
  trace messages.
-/
def antiStackOverflow (m : TransM α) : TransM α := do
  if (<- get).depth >= 500 then
    throwError "recursion depth limit reached :("
  else
    modify (fun s => { s with depth := s.depth + 1})
    let ret <- m
    modify (fun s => { s with depth := s.depth - 1})
    return ret

def TransM.run (m : TransM α) : TacticM α := do
  let state : TransS := {}
  let (ret, _state) <- StateRefT'.run m state
  return ret

def TransM.getState: TransM TransS := get

end HoSmt.Translation
