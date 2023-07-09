import HoSmt
import HoSmt.Tests.Common.All

set_option HoSmt.shouldTranslate true

example: All (. > 0) [1, 2] := by smt

theorem helper : All (. >= x) xs -> All (. >= nat_lit 0) xs := by smt

theorem helper2 : All (. >= 2) [1, 2] -> All (. >= 0) [1, 2] := by smt

example (xs : List Nat) : All (. >= nat_lit 4) xs -> All (. >= nat_lit 4) (xs.map id)
  := by smt[helper, helper2]
