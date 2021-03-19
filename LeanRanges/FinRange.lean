import LeanRanges.ToRange

structure FinRange (n : Nat) where
  start : Nat
  stop  : Nat
  step  : Nat
  ascending : Bool

instance : ToRange (Fin n) (FinRange n) where
  toRange   start stop step := ⟨start, stop,   step.natAbs, step >= 0⟩
  toRangeEq start stop step := ⟨start, stop+1, step.natAbs, step >= 0⟩


-- Lemma to help with FinRange implementation
theorem Nat.ltAddRight (a b c : Nat) (h : a < b) : a < b + c :=
  match c with
  | 0 => h
  | c'+1 =>
    have h₁ : a < (b + c') + 1 := Nat.lt.step (ltAddRight a b c' h)
    have h₂ : (b + c') + 1 = b + (c' + 1) from Nat.add_assoc ..
    cast (congrArg (λ x => a < x) h₂) h₁


namespace Fin

/-- An exclusive range `[start, stop)` of `Fin n` values separated by `step`.

  If `n` is specified and `n < stop` then the range will be truncated to `[start, n)`. -/
def range (start stop : Nat) (step : Nat := 1) (ascending : Bool := true) (n : Nat := stop) : FinRange n :=
  ⟨start, if n < stop then n else stop, step, ascending⟩

/-- An inclusive range `[start, stop]` of `Fin n` values separated by `step`.

  If `n` is specified and `n ≤ stop` then the range will be truncated to `[start, n-1]`. -/
def rangeEq (start stop : Nat) (step : Nat := 1) (ascending : Bool := true) (n : Nat := (Nat.succ stop)) : FinRange n :=
  ⟨start, if n ≤ stop then n else stop+1, step, ascending⟩

-- Fin helpers for FinRange implementation
def nonZero : {n : Nat} → Fin n → n > 0
  | 0, x => Fin.elim0 x
  | n+1, _ => Nat.succPos n

def lift {n : Nat} (m : Nat) : Fin n → Fin (n+m)
  | ⟨v, h⟩ => ⟨v, Nat.ltAddRight v n m h⟩

instance : HasMin (Fin n) where
  minOf x := Fin.ofNat' 0 (nonZero x)

instance : HasMax (Fin n) where
  maxOf x := Fin.ofNat' (n-1) (nonZero x)

end Fin




namespace FinRange
universes u v


@[inline] def steps (r : FinRange n) : Nat :=
  if r.step = 0 then
    0
  else
    let size := r.stop - r.start
    size / r.step + (if size % r.step = 0 then 0 else 1)

def next (r : FinRange n) (i : Fin n) : Fin n :=
  if r.ascending
  then Fin.ofNat' (i.val + r.step) (Fin.nonZero i)
  else Fin.ofNat' (i.val - r.step) (Fin.nonZero i)

def first? (r : FinRange n) : Option (Fin n) :=
  if h : n > 0 then
    if r.ascending then
      Fin.ofNat' r.start h
    else
      Fin.ofNat' (r.start + (r.step * (r.steps - 1))) h
  else
    none

def reverse (r : FinRange n) : FinRange n :=
  {r with ascending := !r.ascending}


@[inline] def forIn {β : Type u} {m : Type u → Type v} [Monad m] (r : FinRange n) (init : β) (f : Fin n → β → m (ForInStep β)) : m β :=
  let rec @[specialize] loop (fuel : Nat) (i : Fin n) (b : β) : m β := do
    match fuel with
    | 0   => pure b
    | fuel+1 => match ← f i b with
      | ForInStep.done b  => pure b
      | ForInStep.yield b => loop fuel (r.next i) b
  match r.first? with
  | none => init
  | some first => loop r.steps first init

instance : ForIn m (FinRange n) (Fin n) where
  forIn := forIn

@[inline] protected def forM {m : Type u → Type v} [Monad m] (r : FinRange n) (f : Nat → m PUnit) : m PUnit :=
  let rec @[specialize] loop (fuel : Nat) (i : Fin n) : m PUnit := do
    match fuel with
    | 0   => pure ⟨⟩
    | fuel+1 => f i; loop fuel (r.next i)
  match r.first? with
  | none => pure ⟨⟩
  | some first => loop r.steps first


def toArray (r : FinRange n) : Array (Fin n) := do
  let mut arr := #[]
  for i in r do
    arr := arr.push i
  arr

def toList (r : FinRange n) : List (Fin n) := do
  let mut l := []
  for i in r.reverse do
    l := i::l
  l

end FinRange
