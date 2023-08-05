import HoSmt
import HoSmt.Tests.Common.Vec
import HoSmt.Tests.Common.All

set_option trace.HoSmt true

set_option HoSmt.shouldTranslate true in
example : ∀xs : List Nat, xs.map (. + nat_lit 1) = [nat_lit 2, nat_lit 3] := by smt


def List.sum : List Nat -> Nat
| .nil => 0
| .cons x xs => x + (sum xs)

/-
% inductive predicate All._uniq.4883._uniq.4910 : (Nat -> Prop) -> List._uniq.4633 -> Prop
thf(ty28, type, glob_All__uniq_4883__uniq_4910 : ((glob_Nat > $o) > (glob_List__uniq_4633 > $o))).

% inductive predicate ctor All.nil._uniq.4883._uniq.4910 : forall {P : Nat -> Prop}, All._uniq.4883._uniq.4910 P List.nil._uniq.4633
thf(ax29, axiom, (![VAR_P : (glob_Nat > $o)]: ((glob_All__uniq_4883__uniq_4910 @ VAR_P) @ glob_List_nil__uniq_4633))).

% inductive predicate ctor All.cons._uniq.4883._uniq.4910 : forall {P : Nat -> Prop} {x : Nat} {xs : List._uniq.4633}, (P x) -> (All._uniq.4883._uniq.4910 P xs) -> (All._uniq.4883._uniq.4910 P (List.cons._uniq.4633 x xs))
thf(ax30, axiom, (![VAR_P : (glob_Nat > $o)]: (![VAR_x : glob_Nat]: (![VAR_xs : glob_List__uniq_4633]: ((VAR_P @ VAR_x) => (((glob_All__uniq_4883__uniq_4910 @ VAR_P) @ VAR_xs) => ((glob_All__uniq_4883__uniq_4910 @ VAR_P) @ ((glob_List_cons__uniq_4633 @ VAR_x) @ VAR_xs)))))))).
-/
set_option HoSmt.shouldTranslate true in
example : (xs : List Nat) -> All (. <= 10) xs -> List.sum xs <= List.length xs * 10 := by
  smt

set_option HoSmt.reconstruct false in
set_option HoSmt.shouldTranslate true in
example : ∀f : Nat -> Nat, f 3 = 4 -> f 3 <= 5 := by smt