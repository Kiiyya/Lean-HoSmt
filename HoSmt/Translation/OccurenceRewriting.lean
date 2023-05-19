import Lean.Elab
import HoSmt.Util
import HoSmt.Translation.TransM

open Lean Elab Term Command Tactic Expr Std
open HoSmt.Util

namespace HoSmt.Translation.OccurenceRewriting

initialize registerTraceClass `HoSmt.Translation.OccurenceRewriting

/--
  Since `rewriter` only applies the rewriting rule to one expression and doesn't recursively descend itself,
  we need to go into each subexpression ourselves.
-/
partial def descendingRewriter (rewriter : Expr -> TransM Expr) (expr : Expr) (traceHint : String := ""): TransM Expr := do
  withTraceNode `HoSmt.Translation.OccurenceRewriting (fun _ => return m!"descendingRewriter{traceHint} {expr}") do
    -- Rewriting with the provided rewriter happens here:
    let expr <- rewriter expr

    -- Then just descend:
    match expr with
    | .forallE var dom body bi => do
      let expr := .forallE var (<- descendingRewriter rewriter dom traceHint) body bi
      let ret <- HoSmt.Util.visitForall expr fun _ body => do
        descendingRewriter rewriter body traceHint
      return ret
    | .lam var dom body bi => do
      let expr := Expr.lam var (<- descendingRewriter rewriter dom traceHint) body bi
      HoSmt.Util.visitLambda' expr fun _ body => do
        descendingRewriter rewriter body traceHint
    | .const .. => return expr
    | .fvar .. => return expr
    | .lit .. => return expr
    | .sort .. => return expr
    | .app fn body => do
      let fn' <- descendingRewriter rewriter fn traceHint
      let body' <- descendingRewriter rewriter body traceHint
      return mkApp fn' body'
    | .mdata md e => return .mdata md <| <- descendingRewriter rewriter e traceHint
    | .proj T idx obj => return .proj T idx <| <- descendingRewriter rewriter obj traceHint
    | _ => throwError "[descendingRewriter{traceHint}] Descending into {expr} not yet supported. Repr is {repr expr}"

/--
  Since `rewriter` only applies the rewriting rule to one expression and doesn't recursively descend itself,
  we need to go into each subexpression ourselves.
-/
partial def descendingRewriter' (expr : Expr) (rewriter : Expr -> TransM Expr) : TransM Expr :=
  descendingRewriter rewriter expr

end HoSmt.Translation.OccurenceRewriting