/-
  Observation functions for extracting results from LogicT computations.
-/
import LogicT.Basic
import LogicT.Instances

namespace LogicT

variable {m : Type → Type} {a : Type}

/-- Extract all results from a `LogicT` computation.

    Warning: will not terminate if the computation produces infinitely many results. -/
unsafe def LogicT.observeAllT [Monad m] (l : LogicT m a) : m (List a) := do
  match ← l.step with
  | none => pure []
  | some (x, rest) => do
    let xs ← rest.observeAllT
    pure (x :: xs)

/-- Extract the first result from a `LogicT` computation,
    returning `none` if there are no results. -/
unsafe def LogicT.observeT [Monad m] (l : LogicT m a) : m (Option a) := do
  match ← l.step with
  | none => pure none
  | some (x, _) => pure (some x)

/-- Extract up to `n` results from a `LogicT` computation. -/
unsafe def LogicT.observeManyT [Monad m] (n : Nat) (l : LogicT m a) : m (List a) :=
  if n == 0 then pure []
  else do
    match ← l.step with
    | none => pure []
    | some (x, rest) => do
      let xs ← rest.observeManyT (n - 1)
      pure (x :: xs)

/-- Type alias for the non-transformer version using `Id`. -/
unsafe abbrev Logic := LogicT Id

/-- Extract all results from a `Logic` computation. -/
unsafe def Logic.observeAll (l : Logic a) : List a :=
  l.observeAllT

/-- Extract the first result from a `Logic` computation,
    returning `none` if there are no results. -/
unsafe def Logic.observe (l : Logic a) : Option a :=
  l.observeT

/-- Extract up to `n` results from a `Logic` computation. -/
unsafe def Logic.observeMany (n : Nat) (l : Logic a) : List a :=
  l.observeManyT n

end LogicT
