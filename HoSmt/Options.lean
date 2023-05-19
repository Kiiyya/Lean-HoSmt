import Lean
open Lean

register_option HoSmt.time : Nat := {
  defValue := 3
  descr := "Timeout for SMT solvers in seconds."
}

register_option HoSmt.cvc5 : String := {
  defValue := "./bin/cvc5"
  descr := "Path to CVC5 binary (try CVC5 v1.0.2 if other versions don't work)."
}

register_option HoSmt.zipperposition : String := {
  defValue := "./bin/zipperposition"
  descr := "Path to Zipperposition binary (Currently not supported)."
}

register_option HoSmt.shouldTranslate : Bool := {
  defValue := false
  descr := "(Used for testing only) When translation succeeds and SMT solver parses it but fails to prove, solve with `sorry` anyway."
}