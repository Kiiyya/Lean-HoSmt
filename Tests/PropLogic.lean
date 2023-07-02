import HoSmt

set_option trace.HoSmt true

example : True ∨ False := by smt


def main : IO Unit := println! "Hewwo"