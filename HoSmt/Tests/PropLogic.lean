import HoSmt
-- import Std.Logic

set_option trace.HoSmt true

abbrev Cl : List Prop -> Prop
| [] => False
| [x] => x
| x :: xs => x ∨ (Cl xs)

def add (a b : Nat) : Nat := a + b

#check Nat

theorem cl_yes {xs : List Prop} (h : x) : x ∈ xs -> Cl xs := by sorry

theorem equiv_pos2 (α β : Prop) : Cl [α ≠ β, ¬α, β] := by sorry
  -- match Classical.em α with
  -- | Or.inl h =>
  --   match Classical.em (α = β) with
  --   | Or.inl h₂ => sorry 
  --   | Or.inr h₂ => simp; exact cl_yes h₂ (List.Mem.head _)
  -- | Or.inr h => exact cl_yes h (List.Mem.tail _ (List.Mem.head _))

/-
unsat
(assume a0 (not (or true false)))
(assume a1 true)
(step t1 (cl (not (= (not (or true false)) false)) (not (not (or true false))) false) :rule equiv_pos2)
(step t2 (cl (= (or true false) true)) :rule all_simplify)
(step t3 (cl (= (not (or true false)) (not true))) :rule cong :premises (t2))
(step t4 (cl (= (not true) false)) :rule all_simplify)
(step t5 (cl (= (not (or true false)) false)) :rule trans :premises (t3 t4))
(step t6 (cl) :rule resolution :premises (t1 t5 a0))
-/
example : Or True False := by smt

example : True ∨ False := by
  have f (a0 : ¬(True ∨ False)) : False := by
    have t1 : Cl [(¬(True ∨ False)) ≠ False, ¬¬(True ∨ False), False] := by exact equiv_pos2 (¬(True ∨ False)) False
    have t2 : Cl [(True ∨ False) = True] := by simp
    have t3 : Cl [(¬(True ∨ False)) = ¬True] := by simp [t2]
    have t4 : Cl [(¬True) = False] := by simp
    have t5 : Cl [(¬ True ∨ False) = False] := by simp
    have t6 : Cl [] := by simp at a0
    exact t6
  simp
#check Classical.not_not

#cvc5 "thf(goal, conjecture, $true | $false)."

