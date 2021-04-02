# A possible common Lean 4 range syntax

An initial proposal for a unified syntax for specifying ranges of various (numeric) types, similar to those found in Rust/Swift/etc, with a bias towards exclusive ranges as the common case, but support for inclusive ranges (which look syntactically similar but distinct) for the case when that is desired (i.e., mainly for finite types).

## Syntax

A proposed syntax equivalent to
  + `[START⋯STOP;STEP]` as Lean 4 syntax for the exclusive range `[START,STOP)` with stride `STEP`, and
  + `[START⋯=STOP;STEP]` as Lean 4 syntax for the inclusive range `[START,STOP]` with stride `STEP`

where `START` and `STOP` are of some type `α` (i.e., the type of values in the range) and `STEP` is an integer which specifies both the distance between values (i.e.,`|STEP|`) and whether the range is in ascending or descending order (i.e., the sign of `STEP`).

The choice of `⋯`, `⋯=`, and `;` as syntactic separators is _somewhat_ arbitrary -- I think there are various different symbols one could debate using. I was basing this off of Rust (which uses `START..STOP` and `START..=STOP`). One could get quite creative... e.g., perhaps reuse `..`, or use `...`? Or perhaps prefer and/or also allow `⋯<` and `⋯=` for consistency? I do think having exclusive/inclusive look _similar_ but _distinct enough_  to not be confused with one another will be valuable for programmers.

I do really like the current range syntax of `[START:STOP:STEP]`, but I couldn't think what a similar but different-enough inclusive range syntax based on that would look like.

Current syntax defined in `LeanRanges/ToRange.lean`

## `TYPE.range` method as a less-cute, more customizable (when needed) interface

It may be valuable for there to also be a `range` method in the namespace of types who implement this syntax as a less-cute but still clear, documented alternative.

I think a good example of this is `Fin.range` (`LeanRanges/FinRange.lean`), which allows us to expose customizations one might want for `Fin` but that are difficult to use with the simpler aforementioned range syntax.

E.g., we can use `Fin.range (n:=a.size) 0 (a.size/2)` to get a range of `Fin a.size` values in `[0, a.size/2)`. More verbose than the terse syntax, yes, but IMO still fairly clear and it requires no proof work, automation, etc.

## What about `STEP = 0`?

Ranges with `STEP = 0` are considered empty. (One could argue this is perhaps consistent with `Nat` division-by-zero defaulting to `0`...?)

## `ToRange` typeclass

A `ToRange` typeclass is used to create ranges from the aforementioned syntax.

See `LeanRanges/ToRange.lean`

## Default upper/lower bounds

Omitting `START` or `STOP` (but not both) is supported via the `HasMax` and `HasMin` type classes (see `LeanRanges/ToRange.lean`) which, given a value of type `α` return the max/min value for that type.

N.B., requiring some value of type `α` instead of being more like the `Inhabited` type class and just having a `min` and `max` value seems like a convenient way to avoid worrying about any inhabitation proofs for `α` regardless of what `α` is. E.g., for `Fin n`, how one can most easily provide evidence for inhabitation can vary depending on the surrounding context, so just taking a `Fin n` seems a simple workaround and is transparent to users.)

## Fixed-width machine integer ranges

The `UInt8Range` implementation (`LeanRanges/UInt8Range.lean`) features some subtle design decisions aimed at keeping all of the arithmetic within the `UInt8` domain. This could use well-founded recursion instead presumably. I got tired of tinkering with that and threw together this approach instead at least for an initial prototype.

The approach for `UInt8Range` should generalize basically unchanged for all `UInt*` types (and `USize`). It's not obvious to me yet whether such a generalization would be cleaner as a huge macro that takes just a few parameters describing the underlying type, or if a typeclass featuring many constraints on the value type (e.g., various homogeneous/heterogenous arithmetic operator constraints, decidable equality, etc etc) would be better. (Also... would the generated code be equivalent either way? Or is there a difference there worth considering for efficiency?)

## A `Range` typeclass?

There is no overarching `Range` typeclass in this proposal at the moment, primarily because the `UInt*` ranges would not fit nicely in the same typeclass as `Nat`, `Int`, and `Fin n`. This is because the unsigned integer ranges are designed carefully to use only fixed-width arithmetic wherever possible, whereas the latter types happily just use `Nat` to determine the size of the range and can more easily encode inclusive ranges by just bumping the ceiling for the range up by `1` (where that's obviously not always possible with a fixed-width integer).

## Examples/Testings

`LeanRanges.lean` has some initial examples/tests. More would be required if this is a direction we want to go.
