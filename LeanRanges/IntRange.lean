import LeanRanges.ToRange

structure IntRange where
  start : Int
  stop  : Int
  step  : Nat
  ascending : Bool

/-- An exclusive range `[start,stop)` of `Int` values separated by `step`. -/
def Int.range (start stop : Int) (step : Nat := 1) (ascending : Bool := true) : IntRange :=
  ⟨start, stop, step, ascending⟩

instance : ToRange Int IntRange where
  toRange start stop step   := Int.range start stop     step.natAbs (step >= 0)
  toRangeEq start stop step := Int.range start (stop+1) step.natAbs (step >= 0)



namespace IntRange
universes u v

/-- `0` if `start >= span`, otherwise `stop - start`. -/
@[inline] def span (r : IntRange) : Nat :=
  match r.stop - r.start with
  | Int.ofNat n => n
  | _ => 0

@[inline] def steps (r : IntRange) : Nat :=
  if r.step = 0 then
    0
  else
    let size := r.span
    size / r.step + (if size % r.step = 0 then 0 else 1)

def next (r : IntRange) (i : Int) : Int :=
  if r.ascending
  then i + r.step
  else i - r.step

def first (r : IntRange) : Int :=
  if r.ascending
  then r.start
  else r.start + (r.step * (r.steps - 1))

def reverse (r : IntRange) : IntRange :=
  {r with ascending := !r.ascending}


@[inline] def forIn {β : Type u} {m : Type u → Type v} [Monad m] (r : IntRange) (init : β) (f : Int → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel : Nat) (i : Int) (b : β) : m β := do
    match fuel with
    | 0   => pure b
    | fuel+1 => match ← f i b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop fuel (r.next i) b
  loop r.steps r.first init

instance : ForIn m IntRange Int where
  forIn := forIn

@[inline] protected def forM {m : Type u → Type v} [Monad m] (r : IntRange) (f : Int → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel : Nat) (i : Int) : m PUnit := do
    match fuel with
    | 0   => pure ⟨⟩
    | fuel+1 => f i; loop fuel (r.next i)
  loop r.steps r.first


def toArray (r : IntRange) : Array Int := do
  let mut arr := #[]
  for i in r do
    arr := arr.push i
  arr

def toList (r : IntRange) : List Int := do
  let mut l := []
  for i in r.reverse do
    l := i::l
  l

end IntRange
