import HoSmt
import HoSmt.Tests.Common.Vec
import HoSmt.Tests.Common.All

set_option HoSmt.shouldTranslate true in
example : ∀xs : List Nat, xs.map (. + 1) = [2, 3] := by smt


def List.sum : List Nat -> Nat
| .nil => 0
| .cons x xs => x + (sum xs)

set_option HoSmt.shouldTranslate true in
theorem th : (xs : List Nat) -> All (. <= 10) xs -> List.sum xs <= List.length xs * 10 := by
  smt