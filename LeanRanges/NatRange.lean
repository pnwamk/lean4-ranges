import LeanRanges.ToRange

namespace Nat

instance : HasMin Nat where
  minOf _ := 0

end Nat


structure NatRange where
  start : Nat
  stop  : Nat
  step  : Nat
  ascending : Bool

/-- An exclusive range `[start,stop)` of `Nat` values separated by `step`. -/
def Nat.range (start stop : Nat) (step : Nat := 1) (ascending : Bool := true) : NatRange :=
  ⟨start, stop, step, ascending⟩

instance : ToRange Nat NatRange where
  toRange start stop step   := Nat.range start stop     step.natAbs (step >= 0)
  toRangeEq start stop step := Nat.range start (stop+1) step.natAbs (step >= 0)


namespace NatRange
universes u v

@[inline] def steps (r : NatRange) : Nat :=
  if r.step = 0 then
    0
  else
    let size := r.stop - r.start
    size / r.step + (if size % r.step = 0 then 0 else 1)

def next (r : NatRange) (i : Nat) : Nat :=
  if r.ascending
  then i + r.step
  else i - r.step

def first (r : NatRange) : Nat :=
  if r.ascending
  then r.start
  else r.start + (r.step * (r.steps - 1))

def reverse (r : NatRange) : NatRange :=
  {r with ascending := !r.ascending}


@[inline] def forIn {β : Type u} {m : Type u → Type v} [Monad m] (r : NatRange) (init : β) (f : Nat → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel i : Nat) (b : β) : m β := do
    match fuel with
    | 0   => pure b
    | fuel+1 => match ← f i b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop fuel (r.next i) b
  loop r.steps r.first init

instance : ForIn m NatRange Nat where
  forIn := forIn

@[inline] protected def forM {m : Type u → Type v} [Monad m] (r : NatRange) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel i : Nat) : m PUnit := do
    match fuel with
    | 0   => pure ⟨⟩
    | fuel+1 => f i; loop fuel (r.next i)
  loop r.steps r.first


def toArray (r : NatRange) : Array Nat := do
  let mut arr := #[]
  for i in r do
    arr := arr.push i
  arr



def toList (r : NatRange) : List Nat := do
  let mut l := []
  for i in r.reverse do
    l := i::l
  l

end NatRange

