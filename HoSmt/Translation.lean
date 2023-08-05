import Lean
import Lean.Data
import HoSmt.Util
import HoSmt.Translation.TransM
import HoSmt.Translation.IndexErasure
import HoSmt.Translation.Monomorphize

open Lean Elab Term Command Tactic Expr Std Meta
open HoSmt Util TermElabM

namespace HoSmt.Translation

initialize registerTraceClass `HoSmt.Translation
initialize registerTraceClass `HoSmt.Translation.sry
initialize registerTraceClass `HoSmt.Translation.traverse

/- Something more structured might be nice, like...
structure Traverser where
  traverseInd (ind : InductiveVal) : TransM InductiveVal
  traverseDef (name : Name) (ty : Expr) (val : Option Expr) : TransM Name
  traverse (e : Expr) : TransM Expr -/

def eraseIndices (e : Expr) : TransM Expr := IndexErasure.traverse e IndexErasure.idPre
def monomorphize (e : Expr) : TransM Expr := Monomorphize.traverse e

def traverse (expr : Expr) : TransM Expr := do
  let expr <- eraseIndices expr
  let expr <- monomorphize expr
  return expr

def translateGoal (g : MVarId) : TransM MVarId := do
  let φ <- g.getType
  let φ' <- traverse φ
  if φ != φ' then
    let g' <- Meta.mkFreshExprMVar (some φ')
    admitGoal g
    replaceMainGoal [g'.mvarId!]
    return g'.mvarId!
  else
    return g

def translateConst (n : Name) : TransM Name := do
  let n := (<- IndexErasure.traverseConst n) |>.getD n
  let n <- Monomorphize.traverseConst n
  return n

end Translation

