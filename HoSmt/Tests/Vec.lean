import HoSmt
import HoSmt.Tests.Common.Vec

set_option trace.HoSmt true

theorem simple : ∀v : Vec Nat n, v = v := by smt

