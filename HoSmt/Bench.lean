import Lean
import HoSmt
import Mathlib

namespace HoSmt.Bench

open Lean Elab Term Command Tactic Expr HoSmt.Translation Std

def getTheoremsFromModule [Monad m] [MonadEnv m] [MonadError m] (moduleName : Name) : m (Array Name) := do
  let env <- getEnv
  let some modIdx := env.getModuleIdx? moduleName | throwError "No such module {moduleName}"
  let decls := env.declsInModuleIdx modIdx
  let decls' <- decls.filterM fun name => do
    if name.isInternal then return false
    if let .thmInfo _thm := <- getConstInfo name then return true
    else return false
  return decls'.toArray

/-- Just so that `#eval` doesn't get confused. -/
def getTheoremsFromModule' (moduleName : Name) : MetaM (Array Name) := getTheoremsFromModule moduleName

def hasPrefix (pre : Name) (name : Name) : Bool :=
  let comps := name.components.toArray
  let preComps := pre.components.toArray
  comps[:preComps.size] == preComps

inductive HoSmtResult (ε : Type u)
| translationFailure (error : ε)
/-- No more goals remaining -/
| solved
/-- Goals remaining -/
| notSolved

/--
  # Benchmarking tactic
  Works on *moduels*, not namespaces!

  Grabs all currently included modules matching the prefix given, and runs the HoSmt on it.
  Reports simple statistics.
  You can optionally also pass in helper lemmas.
  ```
  #bench `Mathlib.Algebra.Group -- matches only one module
  #bench `Mathlib.Algebra [Nat.add_comm] -- give helper lemmas
  ```
-/
elab "#bench " pre:name modlimit?:("modlimit=" num)? auxes?:(smtArgs)? : command => do
  let env <- getEnv
  let pre := pre.getName
  if pre.isAnonymous then
    throwError "Please specify some module prefix such as `Mathlib.Data.Int"
  
  Command.liftTermElabM do
    -- Add auxiliary lemmas explicitly provided by the user.
    let auxes <- auxes? |>.map (fun x => x.raw[1]) |>.map Syntax.getSepArgs |>.getD #[] |>.mapM fun aux => do
      if let .ident _ _ th .. := aux then return th
      let aux <- elabTerm aux none
      if let some (name, _) := aux.const? then return name
      else HoSmt.defineExpression aux

    let mut mathlibModules := env.allImportedModuleNames |>.filter (hasPrefix pre .)
    let limit := modlimit?.map (fun x => x.raw[1]!.toNat) |>.getD 3
    if mathlibModules.size > limit then
      mathlibModules := mathlibModules[:limit]
      trace[HoSmt.bench] "Too many modules, truncating to just {mathlibModules}"
    let theorems <- mathlibModules.concatMapM getTheoremsFromModule

    trace[HoSmt.bench] "Have {theorems.size} theorems from {mathlibModules.size} modules {mathlibModules}"
    
    let report <- theorems.mapM fun th => do
      try
        let info <- getConstInfo th
        let goal <- Meta.mkFreshExprMVar (some info.type)
        let outputGoals <- Tactic.run (goal.mvarId!) <| withEnvSandbox do
          let log
          | .ok (.proof _) => return m!"Proved {th}"
          | .ok (.gaveUp _) => return m!"Gave up {th}"
          | .ok (.contra _) => return m!"Found contradiction {th}"
          | .error e => return m!"Failed to prove {th}, reason:\n{e.toMessageData}"
          let _ <- withTraceNode `HoSmt log do
            let (tptp, goal') <- HoSmt.leanToTPTP auxes
            trace[HoSmt.Encoding] tptp
            let res <- HoSmt.runSMT tptp
            match res with
            | .proof prf => do
              admitGoal goal' -- "sorry" (no proof reconstruction yet)
              trace[HoSmt.bench] m!"PROOF:\n{prf}"
            | .contra contra => do
              throwError "CONTRADICTON:\n{contra}"
            | .gaveUp msg => trace[HoSmt.bench] "Gave up. msg: {msg}"
            return res
        return (th, if outputGoals.isEmpty then .solved else .notSolved)
      catch e => return (th, HoSmtResult.translationFailure e)
    let n_translated := report.filter (match Prod.snd . with | .translationFailure _ => false | _ => true) |>.size
    let n_proven := report.filter (match Prod.snd . with | .solved => true | _ => false) |>.size
    let percentageTr := (Float.ofNat n_translated) / (Float.ofNat theorems.size)
    let percentagePr := (Float.ofNat n_proven) / (Float.ofNat n_translated)
    logError m!"Translated {n_translated}/{theorems.size} = {percentageTr}, proved {n_proven}/{n_translated} = {percentagePr}"

end Bench

set_option trace.HoSmt true
set_option trace.HoSmt.bench true
set_option trace.HoSmt.debug true
set_option trace.HoSmt.Translation true
set_option trace.HoSmt.Translation.traverse true
set_option trace.HoSmt.Translation.IndexErasure true
set_option trace.HoSmt.Translation.IndexErasure.traverse true
set_option trace.HoSmt.Translation.OccurenceRewriting true
set_option trace.HoSmt.Translation.Mono true
set_option trace.HoSmt.Translation.Mono.indArgs true
set_option trace.HoSmt.Translation.Mono.defArgs true
set_option trace.HoSmt.Translation.sry true
set_option trace.HoSmt.Translation.Mono.traverse true
set_option trace.HoSmt.Translation.Mono.traverseConst true
set_option trace.HoSmt.Util.AddDecl true
set_option trace.HoSmt.Encoding true
set_option trace.HoSmt.Encoding.traverse true
set_option trace.HoSmt.Encoding.appendItem true
set_option trace.HoSmt.Encoding.defEqns true

set_option maxHeartbeats 99999999
set_option HoSmt.time 2
set_option HoSmt.cvc5 "./bin/cvc5"


#exit

-- Should maybe create a lake script to run these and produce nice machine-readable reports instead.

-- #bench `Mathlib.Algebra
-- #bench `Mathlib.Algebra.Group.Commutator
-- #bench `Mathlib.Algebra.Group.Commute
-- #bench `Mathlib.Algebra.Group.Conj
-- #bench `Mathlib.Algebra.Group.ConjFinite

-- #bench `Mathlib.Data.Int.Dvd
-- #bench `Mathlib.Algebra
-- #bench `Mathlib.Analysis.Convex.Basic
-- #bench `Mathlib.Algebra.Group

