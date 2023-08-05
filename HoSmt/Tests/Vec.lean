import HoSmt
import HoSmt.Tests.Common.Vec

set_option trace.HoSmt true

theorem simple : ∀v : Vec Nat n, v = v := by smt

inductive All (P : α -> Prop) : Vec α n -> Prop
| nil : All P Vec.nil
| cons : P x -> All P xs -> All P (Vec.cons x xs)

-- The following translates but cvc5 fails to find a proof :(
set_option HoSmt.shouldTranslate true in
example: ∀v : Vec Nat n, All (. <= 10) v -> sum v <= 10 * n := by smt

