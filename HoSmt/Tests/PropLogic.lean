import HoSmt
import Duper.Tactic
import HoSmt.Decode.Rules

open HoSmt.Decode.Rules

set_option trace.HoSmt true
set_option trace.HoSmt.Decode true
set_option HoSmt.reconstruct true

set_option linter.unusedVariables false

theorem test : True ∨ False := by smt
#print axioms test
example : True ∨ False ∨ False  := by smt
example : False ∨ (True = ¬False) := by smt

open HoSmt.Decode.Alethe2
theorem test2 : ∀x: Prop, x = x := by smtProof
  unsat
  (assume a0 (not (forall ((VAR_x Bool)) (= VAR_x VAR_x))))
  (assume a1 true)
  (step t1 (cl (not (= (not (forall ((VAR_x Bool)) (= VAR_x VAR_x))) false)) (not (not (forall ((VAR_x Bool)) (= VAR_x VAR_x)))) false) :rule equiv_pos2)
  
  (anchor :step t2 :args ((:= (VAR_x Bool) VAR_x)))
  (step t2.t1 (cl (= VAR_x VAR_x)) :rule refl)
  (step t2.t2 (cl (= (= VAR_x VAR_x) true)) :rule all_simplify)
  (step t2 (cl (= (forall ((VAR_x Bool)) (= VAR_x VAR_x)) (forall ((VAR_x Bool)) true))) :rule bind)
  
  (step t3 (cl (= (forall ((VAR_x Bool)) true) true)) :rule all_simplify)
  (step t4 (cl (= (forall ((VAR_x Bool)) (= VAR_x VAR_x)) true)) :rule trans :premises (t2 t3))
  (step t5 (cl (= (not (forall ((VAR_x Bool)) (= VAR_x VAR_x))) (not true))) :rule cong :premises (t4))
  (step t6 (cl (= (not true) false)) :rule all_simplify)
  (step t7 (cl (= (not (forall ((VAR_x Bool)) (= VAR_x VAR_x))) false)) :rule trans :premises (t5 t6))
  (step t8 (cl) :rule resolution :premises (t1 t7 a0))

example : ∀x: Prop, x = x := by smt

example : ∀x, False ∨ (x = True) ∨ (x = ¬True) := by smtProof
  unsat
  (assume a0 (not (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true)))))))
  (assume a1 true)
  (step t1 (cl
    (not (= (not (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true)))))) false))
    (not (not (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true))))))) false)
    :rule equiv_pos2)
  (anchor :step t2 :args ((:= (VAR_x Bool) VAR_x)))
  (step t2.t1 (cl (= VAR_x VAR_x)) :rule refl)
  (step t2.t2 (cl (= (or false (or (= VAR_x true) (= VAR_x (not true)))) (or (= VAR_x true) (= VAR_x (not true))))) :rule all_simplify)
  (step t2.t3 (cl (= (= VAR_x true) VAR_x)) :rule all_simplify)
  (step t2.t4 (cl (= VAR_x VAR_x)) :rule refl)
  (step t2.t5 (cl (= (not true) false)) :rule all_simplify)
  (step t2.t6 (cl (= (= VAR_x (not true)) (= VAR_x false))) :rule cong :premises (t2.t4 t2.t5))
  (step t2.t7 (cl (= (= VAR_x false) (not VAR_x))) :rule all_simplify)
  (step t2.t8 (cl (= (= VAR_x (not true)) (not VAR_x))) :rule trans :premises (t2.t6 t2.t7))
  (step t2.t9 (cl (= (or (= VAR_x true) (= VAR_x (not true))) (or VAR_x (not VAR_x)))) :rule cong :premises (t2.t3 t2.t8))
  (step t2.t10 (cl (= (or false (or (= VAR_x true) (= VAR_x (not true)))) (or VAR_x (not VAR_x)))) :rule trans :premises (t2.t2 t2.t9))
  (step t2 (cl (= (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true))))) (forall ((VAR_x Bool)) (or VAR_x (not VAR_x))))) :rule bind)
  (step t3 (cl (= (forall ((VAR_x Bool)) (or VAR_x (not VAR_x))) (forall ((VAR_x Bool)) true))) :rule all_simplify)
  (step t4 (cl (= (forall ((VAR_x Bool)) true) true)) :rule all_simplify)
  (step t5 (cl (= (forall ((VAR_x Bool)) (or VAR_x (not VAR_x))) true)) :rule trans :premises (t3 t4))
  (step t6 (cl (= (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true))))) true)) :rule trans :premises (t2 t5))
  (step t7 (cl (= (not (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true)))))) (not true))) :rule cong :premises (t6))
  (step t8 (cl (= (not true) false)) :rule all_simplify)
  (step t9 (cl (= (not (forall ((VAR_x Bool)) (or false (or (= VAR_x true) (= VAR_x (not true)))))) false)) :rule trans :premises (t7 t8))
  (step t10 (cl) :rule resolution :premises (t1 t9 a0))

/- Generates the following TPTP input:
% inductive Nat : Type
thf(ty0, type, glob_Nat : $tType).
% ctor Nat.zero : Nat
thf(ty1, type, glob_Nat_zero : glob_Nat).
% ctor Nat.succ : Nat -> Nat
thf(ty2, type, glob_Nat_succ : (glob_Nat > glob_Nat)).
% axiom Nat.succ.injEq : forall (n : Nat) (n_1 : Nat), Eq.{1} Prop (Eq.{1} Nat (Nat.succ n) (Nat.succ n_1)) (Eq.{1} Nat n n_1)
thf(ax3, axiom, (![VAR_n : glob_Nat]: (![VAR_n__uniq_39302 : glob_Nat]: (((glob_Nat_succ @ VAR_n) = (glob_Nat_succ @ VAR_n__uniq_39302)) = (VAR_n = VAR_n__uniq_39302))))).
thf(goal, conjecture, (![VAR_n : glob_Nat]: (VAR_n = VAR_n))).
-/
set_option HoSmt.reconstruct false in
example : ∀n : Nat, n = n := by smt

-- example : ∀n : Nat, n = n := by
--   smtProof
--     unsat
--     -- TODO: Problem is this extra assume, which doesn't vibe with smt_harness
--     (assume a0 (forall ((VAR_n glob_Nat)) (forall ((VAR_n__uniq_39302 glob_Nat)) (= (= (@ glob_Nat_succ VAR_n) (@ glob_Nat_succ VAR_n__uniq_39302)) (= VAR_n VAR_n__uniq_39302)))))
--     (assume a1 (not (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n))))
--     (assume a2 true)
--     (step t1 (cl (not (= (not (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n))) false)) (not (not (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n)))) false) :rule equiv_pos2)
--     (anchor :step t2 :args ((:= (VAR_n glob_Nat) VAR_n)))
--     (step t2.t1 (cl (= VAR_n VAR_n)) :rule refl)
--     (step t2.t2 (cl (= (= VAR_n VAR_n) true)) :rule all_simplify)
--     (step t2 (cl (= (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n)) (forall ((VAR_n glob_Nat)) true))) :rule bind)
--     (step t3 (cl (= (forall ((VAR_n glob_Nat)) true) true)) :rule all_simplify)
--     (step t4 (cl (= (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n)) true)) :rule trans :premises (t2 t3))
--     (step t5 (cl (= (not (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n))) (not true))) :rule cong :premises (t4))
--     (step t6 (cl (= (not true) false)) :rule all_simplify)
--     (step t7 (cl (= (not (forall ((VAR_n glob_Nat)) (= VAR_n VAR_n))) false)) :rule trans :premises (t5 t6))
--     (step t8 (cl) :rule resolution :premises (t1 t7 a1))
--   done

