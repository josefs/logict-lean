/-
  Observation functions for extracting results from LogicT computations.

  Each observation function fixes `r` to an appropriate type:
  - `observeAllT`: `r = List a`
  - `observeT`: `r = Option a`
  - `observeManyT`: `r = List a`
-/
import LogicT.Basic
import LogicT.Operations

namespace LogicT

variable {m : Type → Type} {a : Type}

/-- Extract the first result from a `LogicT` computation,
    returning `none` if there are no results. Fixes `r = Option a`. -/
def observeT [Monad m] (l : LogicT (Option a) m a) : m (Option a) :=
  l (fun a _ => pure (some a)) (pure none)

/-- Extract up to `n` results from a `LogicT` computation. Fixes `r = List a`. -/
def observeManyT [Monad m] (n : Nat) (l : LogicT (List a) m a) : m (List a) := do
  let all ← observeAllT l
  pure (all.take n)

/-- Type alias for the non-transformer version using `Id` with `r = List a`.
    `Logic a` computations can use `do` notation, `<|>`, etc. since
    `Monad (LogicT (List a) Id)` is available. -/
abbrev Logic (a : Type) := LogicT (List a) Id a

/-- Extract all results from a `Logic` computation. -/
def Logic.observeAll (l : Logic a) : List a :=
  observeAllT l

/-- Extract the first result from a `Logic` computation,
    returning `none` if there are no results. -/
def Logic.observe (l : Logic a) : Option a :=
  match observeAllT l with
  | [] => none
  | x :: _ => some x

/-- Extract up to `n` results from a `Logic` computation. -/
def Logic.observeMany (n : Nat) (l : Logic a) : List a :=
  observeManyT n l

end LogicT
