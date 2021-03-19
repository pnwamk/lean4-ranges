


class HasMax (α : Type u) where
  /-- Returns the maximum value of the same type. -/
  maxOf : α → α


class HasMin (α : Type u) where
  /-- Returns the minimum value of the same type. -/
  minOf : α → α


class ToRange (α : Type u) (ρ : outParam (Type v)) : Type (max u v) where
  /-- `toRange start stop step` creates an exclusive range of values (i.e.,
      in `[start,stop)`). The magnitude of `step` determines the
      difference between values while the sign dictates the order in which the values
      are enumerated (positive from low to high, negative from high to
      low, zero implying an empty range). -/
  toRange : α → α → Int → ρ
  /-- `toRangeEq start stop step` is like `toRange`, but creates an inclusive range of values (i.e.,
      in `[start,stop]`). -/
  toRangeEq : α → α → Int → ρ

namespace ToRange

-- exclusive range syntax
syntax:max "[" term "⋯" "]" : term
syntax:max "[" "⋯" term "]" : term
syntax:max "[" term "⋯" term "]" : term
syntax:max "[" term "⋯" ";" term "]" : term
syntax:max "[" "⋯" term ";" term "]" : term
syntax:max "[" term "⋯" term ";" term "]" : term
-- inclusive range syntax
syntax:max "[" "⋯=" term "]" : term
syntax:max "[" term "⋯=" term "]" : term
syntax:max "[" "⋯=" term ";" term "]" : term
syntax:max "[" term "⋯=" term ";" term "]" : term

open HasMin HasMax

macro_rules
  -- exclusive range syntax
  | `([$start ⋯ ]) => `(let x := $start; toRange x (maxOf x) 1)
  | `([ ⋯ $stop])  => `(let x := $stop; toRange (minOf x) x 1)
  | `([ $start ⋯ $stop ]) => `(toRange $start $stop 1)
  | `([$start ⋯ ; $step]) => `(let x := $start; toRange x (maxOf x) $step)
  | `([ ⋯ $stop ; $step ]) => `(let x := $stop; toRange (minOf x) x $step)
  | `([ $start ⋯ $stop ; $step ]) => `(toRange $start $stop $step)
  -- inclusive range syntax
  | `([ ⋯= $stop])  => `(let x := $stop; toRangeEq (minOf x) x 1)
  | `([ $start ⋯= $stop ]) => `(toRangeEq $start $stop 1)
  | `([ ⋯= $stop ; $step ]) => `(let x := $stop; toRangeEq (minOf x) x $step)
  | `([ $start ⋯= $stop ; $step ]) => `(toRangeEq $start $stop $step)

end ToRange
