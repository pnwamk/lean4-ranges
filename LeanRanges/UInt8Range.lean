import LeanRanges.ToRange


structure UInt8Range where
  /-- Lower bound for the range. -/
  start : UInt8
  /-- Upper bound for the range. -/
  stop  : UInt8
  /-- Distance between values in the range. `step = 0` means
    the range is empty regardless of `start` and `stop`. -/
  step  : UInt8
  /-- If `true` the range values are visited in ascending order,
    otherwise they are visited in descending order. -/
  ascending : Bool
  /-- If `true` then `stop` is an exclusive upper bound,
    otherwise `stop` is an inclusive upper bound. -/
  exclusive : Bool


namespace UInt8

instance : HasMin UInt8 where
  minOf _ := 0

instance : HasMax UInt8 where
  maxOf _ := UInt8.ofNat (UInt8.size - 1)

/-- An exclusive range `[start,stop)` of `UInt8` values separated by `step`. -/
def range (start stop : UInt8) (step : UInt8 := 1) (ascending : Bool := true) : UInt8Range := {
  start := start,
  stop := stop,
  step := step,
  ascending := ascending,
  exclusive := true
  }

/-- An inclusive range `[start,stop]` of `UInt8` values separated by `step`. -/
def rangeEq (start stop : UInt8) (step : UInt8 := 1) (ascending : Bool := true) : UInt8Range := {
  start := start,
  stop := stop,
  step := step,
  ascending := ascending,
  exclusive := false
  }

end UInt8


instance : ToRange UInt8 UInt8Range where
  toRange start stop step :=
    let stepAbs := step.natAbs
    let ascending := step >= 0
    let step := if stepAbs >= UInt8.size
                then UInt8.ofNat (UInt8.size - 1)
                else UInt8.ofNat stepAbs
    UInt8.range start stop step ascending
  toRangeEq start stop step :=
    let stepAbs := step.natAbs
    let ascending := step >= 0
    if stepAbs >= UInt8.size then
      UInt8.range start stop (UInt8.ofNat (UInt8.size - 1)) ascending
    else
      UInt8.rangeEq start stop (UInt8.ofNat stepAbs) ascending


namespace UInt8Range
universes u v

/-- `0` if `start >= span`, otherwise `stop - start`. -/
@[inline] def span (r : UInt8Range) : UInt8 :=
  if r.start >= r.stop then 0 else r.stop - r.start

/-- For exclusive ranges: returns the number of values in the range.
  For inclusive ranges: if `step = 0` the returned value is meaningless,
  otherwise the number returned is one less than the number of values
  in the range.  -/
@[inline] def steps (r : UInt8Range) : UInt8 := do
  if r.step = 0 then
    0
  else
    let size := r.span
    size / r.step + (if r.exclusive && size % r.step != 0 then 1 else 0)

/-- If `next r i = i'` where `i` is a valid non-final value of the
 the range `r`, then `i'` is the next value in the range. -/
def next (r : UInt8Range) (i : UInt8) : UInt8 :=
  if r.ascending
  then i + r.step
  else i - r.step

/-- The first value in the range; if `step = 0` the value is meaningless.-/
def first (r : UInt8Range) : UInt8 :=
  if r.ascending then
    r.start
  else do
    let mut n := r.start + (r.step * (r.steps - 1))
    if !r.exclusive && (n + r.step <= r.stop) then
      n + r.step
    else
      n

def reverse (r : UInt8Range) : UInt8Range :=
  {r with ascending := !r.ascending}



-- -- -- -- -- -- -- -- -- -- -- --
-- ForIn
-- -- -- -- -- -- -- -- -- -- -- --


-- For exclusive ranges, `steps` is the exact number of values in the range, so
-- we use that directly to determine the number of iterations.
@[inline] unsafe def forInLtUnsafe {β : Type u} {m : Type u → Type v} [Monad m] (r : UInt8Range) (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel i : UInt8) (b : β) : m β := do
    if fuel = 0 then pure b
    else match ← f i b with
         | ForInStep.done b  => pure b
         | ForInStep.yield b => loop (fuel - 1) (r.next i) b
  loop r.steps r.first init

/- Reference implementation for inclusive `forIn` -/
@[implementedBy UInt8Range.forInLtUnsafe]
def forInLt {β : Type u} {m : Type u → Type v} [Monad m] (r : UInt8Range) (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel : Nat) (i : UInt8) (b : β) : m β := do
    match fuel with
    | 0 => pure b
    | fuel+1 =>
      match ← f i b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop fuel (r.next i) b
  loop r.steps.toNat r.first init

-- For inclusive ranges, if `step = 0` the range is empty, otherwise `steps` is
-- one less than the number of values in the range, and so our loop ends up
-- looking more like a "do-while" loop than the exclusive range sister function,
-- featuring an initial guard outside of the loop checking for when `step = 0`,
-- and within the loop we check _after_ each iteration, allowing us to use
-- UInt8 as the our fuel!
@[inline] unsafe def forInEqUnsafe {β : Type u} {m : Type u → Type v} [Monad m] (r : UInt8Range) (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  if r.step = 0 then pure init else
  let rec @[specialize] loop (fuel i : UInt8) (b : β) : m β := do
    match ← f i b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b =>
      if fuel = 0 then pure b
      else loop (fuel - 1) (r.next i) b
  loop r.steps r.first init

/- Reference implementation for inclusive `forIn` -/
@[implementedBy UInt8Range.forInEq]
def forInEq {β : Type u} {m : Type u → Type v} [Monad m] (r : UInt8Range) (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  if r.step = 0 then pure init else
  let rec @[specialize] loop (fuel : Nat) (i : UInt8) (b : β) : m β := do
    match ← f i b with
    | ForInStep.done b  => pure b
    | ForInStep.yield b =>
      match fuel with
      | 0 => pure b
      | fuel+1 => loop fuel (r.next i) b
  loop r.steps.toNat r.first init


@[inline] def forIn {β : Type u} {m : Type u → Type v} [Monad m] (r : UInt8Range) (init : β) (f : UInt8 → β → m (ForInStep β)) : m β :=
  if r.exclusive then
    forInLt r init f
  else
    forInEq r init f


instance : ForIn m UInt8Range UInt8 where
  forIn := forIn


-- -- -- -- -- -- -- -- -- -- -- --
-- ForM
-- -- -- -- -- -- -- -- -- -- -- --
-- See ForIn comments regarding ForM[Lt|Eq] implementation differences

@[inline] unsafe def forMLtUnsafe {m : Type u → Type v} [Monad m] (r : UInt8Range) (f : UInt8 → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel i : UInt8) : m PUnit := do
    if fuel = 0 then pure ⟨⟩
    else do f i; loop (fuel - 1) (r.next i)
  loop r.steps r.first

/- Reference implementation for `forMLt` -/
@[implementedBy UInt8Range.forMLtUnsafe]
def forMLt {m : Type u → Type v} [Monad m] (r : UInt8Range) (f : UInt8 → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel : Nat) (i : UInt8) : m PUnit := do
    match fuel with
    | 0 => pure ⟨⟩
    | fuel+1 => do f i; loop fuel (r.next i)
  loop r.steps.toNat r.first


@[inline] unsafe def forMEqUnsafe {m : Type u → Type v} [Monad m] (r : UInt8Range) (f : UInt8 → m PUnit) : m PUnit :=
  if r.step = 0 then pure ⟨⟩ else
  let rec @[specialize] loop (fuel i : UInt8) : m PUnit := do
    f i
    if fuel = 0 then pure ⟨⟩
    else loop (fuel - 1) (r.next i)
  loop r.steps r.first

/- Reference implementation for `forMEq` -/
@[implementedBy UInt8Range.forMEqUnsafe]
def forMEq {m : Type u → Type v} [Monad m] (r : UInt8Range) (f : UInt8 → m PUnit) : m PUnit :=
  if r.step = 0 then pure ⟨⟩ else
  let rec @[specialize] loop (fuel : Nat) (i : UInt8) : m PUnit := do
    f i
    match fuel with
    | 0 => pure ⟨⟩
    | fuel+1 => loop fuel (r.next i)
  loop r.steps.toNat r.first


@[inline] def forM {m : Type u → Type v} [Monad m] (r : UInt8Range) (f : UInt8 → m PUnit) : m PUnit :=
  if r.exclusive then
    forMLt r f
  else
    forMEq r f

instance : ForM m UInt8Range UInt8 where
  forM := forM

def toArray (r : UInt8Range) : Array UInt8 := do
  let mut arr := #[]
  for i in r do
    arr := arr.push i
  arr

def toList (r : UInt8Range) : List UInt8 := do
  let mut l := []
  for i in r.reverse do
    l := i::l
  l

end UInt8Range


