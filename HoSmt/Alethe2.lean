import Std
import Megaparsec

def List.flatten : List String -> String
| [] => ""
| x :: xs => x ++ xs.flatten

namespace HoSmt.Alethe2
/-! Parser for the Alethe2 format that is returned by CVC5. -/

open Megaparsec Parsec Common

abbrev P := Parsec Char String Unit

inductive AExpr
| boolean : Bool -> AExpr
| number : Nat -> AExpr
| const : String -> AExpr
| eq (l r : AExpr) : AExpr
| not : AExpr -> AExpr
| cl : List AExpr -> AExpr
  deriving Repr

inductive ACmd
| assume (id : String) (e : AExpr) : ACmd
| step (id : String) (e : AExpr) (rule : String) (args : List AExpr) : ACmd
  deriving Repr

partial def AExpr.toString : AExpr -> String
| .boolean b => ToString.toString b
| .number n => ToString.toString n
| .const c => c
| .eq l r => s!"(= {l.toString} {r.toString})"
| .not e => s!"(not {e.toString})"
| .cl cls => s!"(cl {cls.map toString |>.intersperse " " |>.flatten})"

instance : ToString AExpr := ⟨AExpr.toString⟩

def ACmd.toString : ACmd -> String
| .assume id e => s!"(assume {id} {e})"
| .step id e rule [] => s!"(step {id} {e} :rule {rule})"
| .step id e rule args => s!"(step {id} {e} :rule {rule} :args {args.map AExpr.toString |>.intersperse " " |>.flatten})"

instance : ToString ACmd := ⟨ACmd.toString⟩

def blanksP : P Unit := do
  discard $ many' (satisfy fun c => [' ', '\n', '\t'].contains c)

def numP : P AExpr := do
  let x : List Char <- some' (satisfy Char.isDigit)
  let str : String := String.mk x
  return .number str.toNat!

def boolP : P AExpr := do
  let s <- string "true" <|> string "false"
  match s with
  | "true" => return .boolean true
  | "false" => return .boolean false
  | _ => unreachable!

def symP : P String := do
  let c : Char <- satisfy Char.isAlpha
  let cs : List Char <- some' (satisfy fun c => c.isAlphanum || c == '=')
  return String.mk (c :: cs)

mutual
  partial def exprLongP : P AExpr := do
    discard <| single '('
    blanksP
    let f : String <- string "not" <|> string "=" <|> string "cl"
    let ret <- match f with
    | "not" => pure <| .not (<- exprP)
    | "=" => pure <| .eq (<- exprP) (<- exprP)
    | "cl" => do
      blanksP
      let cls : List AExpr <- many' exprP
      pure <| .cl cls
    | _ => unreachable!
    discard <| single ')'
    return ret

  partial def exprP : P AExpr := blanksP *> (numP <|> boolP <|> exprLongP) <* blanksP
end

#eval discard <| parseTestP exprP " (not true )"
#eval discard <| parseTestP exprP " (not (= 123 566) ) "
#eval discard <| parseTestP exprP " (cl 1 (cl) 123) "
#eval discard <| parseTestP exprP " (cl (cl) 12345) "
#eval discard <| parseTestP exprP " (cl (cl) (cl )) "

def cmdP : P ACmd := do
  discard $ single '('
  let cmd <- blanksP *> string "assume" <|> string "step"
  let id <- blanksP *> symP
  let ret <- match cmd with
  | "assume" => pure <| .assume id (<- exprP)
  | "step" => do
    let e <- exprP
    discard <| blanksP *> string ":rule"
    let rule <- blanksP *> symP
    blanksP
    let args : Option (List AExpr) <- option <| string ":args" *> blanksP *> many' exprP
    blanksP
    pure <| .step id e rule (args.getD [])
  | _ => unreachable!
  discard $ single ')'
  return ret

#eval parseTestP cmdP "(assume a1 true)"
#eval parseTestP cmdP "(step a1 true :rule resolution)"
#eval parseTestP cmdP "(step a1 true :rule resolution :args true false)"

end HoSmt.Alethe2