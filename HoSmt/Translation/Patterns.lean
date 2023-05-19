import HoSmt.Translation.TransM

open HoSmt Translation

namespace HoSmt.Translation.Patterns

/--
Removes items which are marked with `false` in the pattern.
If pattern is shorter than `xs`, extends the pattern with `true`s.
```
xs      = [x₁,    x₂,   x₃]
pattern = [true, false, true]
output  = [x₁,          x₃]
```

A `true` in the pattern means that this argument is being monomorphized.
This function is used for grabbing a few binders from a binder telescope.
As such, the "default" is `false`.
-/
def filterByPattern : (xs : List α) -> (pattern : List <| Bool) -> TransM <| List α
| _x :: xs, false :: pattern => filterByPattern xs pattern
| x  :: xs, true  :: pattern => return x :: (<- filterByPattern xs pattern)
| _rest   , pattern          => do
  if pattern.any id then throwError s!"pattern still has `true` but end of xs."
  else return []

/--
Keeps items marked with `false`.

Removes items which are marked with `true`. If `xs` is longer than `pattern`, then
assumes pattern is filled with `false`s.

This function is used for grabbing all binders in a binder telescope, which have not been
grabbed by `filterByPattern`, so it is its complement.
-/
def filterByPatternInv : (xs : List α) -> (pattern : List Bool) -> TransM <| List α
| _x :: xs, true  :: pattern => filterByPatternInv xs pattern
| x  :: xs, false :: pattern => return x :: (<- filterByPatternInv xs pattern)
| rest    , _pattern          => return rest
  -- if pattern.any not then throwError s!"pattern still has `false` but end of xs."
  -- else return rest

/--
Turns every occurence of `true` into a `some x`, and `false` into a `none`.
Extends pattern with `false` if necessary.
-/
def stencilPattern : (xs : List α) -> (pattern : List Bool) -> TransM <| List (Option α)
| x :: xs, true  :: pattern => return (some x) :: (<- stencilPattern xs pattern)
| _ :: xs, false :: pattern => return none     :: (<- stencilPattern xs pattern)
| _      , pattern          => do
  if pattern.any id then throwError "pattern still has `true`, but ran out of xs."
  else return []

end HoSmt.Translation.Patterns