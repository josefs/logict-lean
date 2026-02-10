/-
  LogicT: A backtracking, logic-programming monad transformer for Lean 4.

  Based on the Haskell `logict` library, adapted from the paper
  "Backtracking, Interleaving, and Terminating Monad Transformers"
  by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry.

  `LogicT m a` is a monad transformer for performing search / backtracking
  computations layered over another monad `m`. When `m = Id`, `LogicT m`
  is isomorphic to a lazy list.

  The representation is a lazy stream with three constructors:
  - `nil`: no results
  - `cons`: a result followed by more results
  - `liftM`: a monadic action producing more stream
-/

namespace LogicT

/-- A monad transformer for performing backtracking computations
    layered over another monad `m`.

    A `LogicT m a` represents a nondeterministic computation that can
    produce zero or more results of type `a`, with effects in `m`.

    When `m = Id`, `LogicT m` is isomorphic to a lazy list.
    For non-trivial `m`, it behaves like a list whose pattern matching
    causes monadic effects.

    Uses `unsafe inductive` because the type nests recursively through `m`,
    which Lean's positivity checker cannot verify in general. The API is safe
    to use; the unsafety is an implementation detail. -/
unsafe inductive LogicT (m : Type → Type) (a : Type) : Type where
  /-- No results. -/
  | nil : LogicT m a
  /-- A result `head` followed by more results `tail`. -/
  | cons (head : a) (tail : LogicT m a) : LogicT m a
  /-- A monadic action that produces more stream. -/
  | liftM (action : m (LogicT m a)) : LogicT m a

variable {m : Type → Type} {a b : Type}

unsafe instance [Pure m] : Inhabited (LogicT m a) := ⟨.nil⟩

/-- Concatenate two `LogicT` computations: produce results from `l₁`, then `l₂`. -/
unsafe def LogicT.append [Functor m] : LogicT m a → LogicT m a → LogicT m a
  | .nil, l₂ => l₂
  | .cons x rest, l₂ => .cons x (LogicT.append rest l₂)
  | .liftM action, l₂ => .liftM ((· |>.append l₂) <$> action)

/-- Map a function over all results. -/
unsafe def LogicT.map' [Functor m] (f : a → b) : LogicT m a → LogicT m b
  | .nil => .nil
  | .cons x rest => .cons (f x) (LogicT.map' f rest)
  | .liftM action => .liftM (LogicT.map' f <$> action)

/-- Monadic bind: for each result of `l`, run `f` and collect all results. -/
unsafe def LogicT.bind' [Monad m] : LogicT m a → (a → LogicT m b) → LogicT m b
  | .nil, _ => .nil
  | .cons x rest, f => LogicT.append (f x) (LogicT.bind' rest f)
  | .liftM action, f => .liftM ((·.bind' f) <$> action)

unsafe instance [Monad m] : Monad (LogicT m) where
  pure x := .cons x .nil
  bind := LogicT.bind'

unsafe instance [Monad m] : Alternative (LogicT m) where
  failure := .nil
  orElse l₁ l₂ := LogicT.append l₁ (l₂ ())

/-- Lift a monadic computation into `LogicT`, producing a single result. -/
unsafe def LogicT.lift [Functor m] (ma : m a) : LogicT m a :=
  .liftM ((fun x => .cons x .nil) <$> ma)

unsafe instance [Monad m] : MonadLift m (LogicT m) where
  monadLift := LogicT.lift

/-- Guard: produce a result only if the condition is true. -/
@[inline]
unsafe def LogicT.guard [Monad m] (p : Bool) : LogicT m Unit :=
  if p then Pure.pure () else .nil

/-- Create a `LogicT` computation from a list of values. -/
unsafe def LogicT.fromList [Monad m] : List a → LogicT m a
  | [] => .nil
  | x :: xs => .cons x (LogicT.fromList xs)

/-- Create a `LogicT` computation from an array of values. -/
unsafe def LogicT.fromArray [Monad m] (xs : Array a) : LogicT m a :=
  LogicT.fromList xs.toList

/-- Choose nondeterministically from a list. -/
unsafe def LogicT.choose [Monad m] (xs : List a) : LogicT m a :=
  LogicT.fromList xs

end LogicT
