import Lean
import Lean.Data
import HoSmt.Util

open Lean Elab Std Tactic Meta

namespace HoSmt.TIP

private partial def encodeExpr (expr : Expr) : TermElabM String :=
  let log
  | .ok val => return m!"{expr} ~~> {val}"
  | .error err => return m!"{expr} ~~> ERROR {err.toMessageData}"
  withTraceNode `HoSmt.Encoding.traverse log do
    match expr with
    | .forallE var dom _ _ => do
      let dom <- encodeExpr dom
      forallBoundedTelescope expr (some 1) fun fvars body => do
        return s!"(forall (({var} {dom})) {<- encodeExpr body})"
    | _ => throwError "not yet implemented"


end TIP