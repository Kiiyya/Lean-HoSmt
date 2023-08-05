import Duper.Tactic

namespace HoSmt.Decode.Rules

/-- The Alethe2 proof rule `equiv_pos2`. -/
theorem equiv_pos2 (α β : Prop) : α ≠ β ∨ ¬α ∨ β := by
  match Classical.em α with
  | Or.inl hα =>
    match Classical.em β with
    | Or.inl hβ => exact Or.inr (Or.inr hβ)
    | Or.inr hβ => simp only [hα, hβ, ne_eq, not_true, true_or]
  | Or.inr hα => exact Or.inr (Or.inl hα)

end HoSmt.Decode.Rules