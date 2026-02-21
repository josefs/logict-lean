/-
  LogicT: A backtracking, logic-programming monad transformer for Lean 4.

  Based on the Haskell `logict` library, adapted from the paper
  "Backtracking, Interleaving, and Terminating Monad Transformers"
  by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry.

  `LogicT r m a` is a monad transformer for performing search / backtracking
  computations layered over another monad `m`. The parameter `r` is the
  result type used in the continuation-passing representation.

  When `m = Id`, `LogicT r Id` is isomorphic to a lazy list.

  The representation uses continuation-passing style (CPS):
    `LogicT r m a = (a → m r → m r) → m r → m r`
  This is safe and does not require `unsafe`.
-/

namespace LogicT

/-- A monad transformer for performing backtracking computations
    layered over another monad `m`.

    A `LogicT r m a` represents a nondeterministic computation that can
    produce zero or more results of type `a`, with effects in `m`.

    Uses continuation-passing style (CPS) representation from the paper.
    The parameter `r` is the result type of the continuation. Observation
    functions fix `r` to a concrete type (e.g. `List a` for `observeAllT`). -/
abbrev LogicT (r : Type) (m : Type → Type) (a : Type) : Type :=
  (a → m r → m r) → m r → m r

variable {r : Type} {m : Type → Type} {a b : Type}

instance : Inhabited (LogicT r m a) := ⟨fun _ nil => nil⟩

/-- Concatenate two `LogicT` computations: produce results from `l₁`, then `l₂`. -/
def append (l₁ l₂ : LogicT r m a) : LogicT r m a :=
  fun cons nil => l₁ cons (l₂ cons nil)

/-- Map a function over all results. -/
def map' (f : a → b) (l : LogicT r m a) : LogicT r m b :=
  fun cons nil => l (fun a mr => cons (f a) mr) nil

/-- Monadic bind: for each result of `l`, run `f` and collect all results. -/
def bind' (l : LogicT r m a) (f : a → LogicT r m b) : LogicT r m b :=
  fun cons nil => l (fun a mr => (f a) cons mr) nil

instance : Monad (LogicT r m) where
  pure x := fun cons nil => cons x nil
  bind := bind'

instance : Alternative (LogicT r m) where
  failure := fun _ nil => nil
  orElse l₁ l₂ := append l₁ (l₂ ())

/-- Lift a monadic computation into `LogicT`, producing a single result. -/
def lift [Monad m] (ma : m a) : LogicT r m a :=
  fun cons nil => ma >>= fun x => cons x nil

instance [Monad m] : MonadLift m (LogicT r m) where
  monadLift := lift

/-- Guard: produce a result only if the condition is true. -/
@[inline]
def guard (p : Bool) : LogicT r m Unit :=
  if p then Pure.pure () else failure

/-- Create a `LogicT` computation from a list of values. -/
def fromList : List a → LogicT r m a
  | [] => failure
  | x :: xs => Pure.pure x <|> fromList xs

/-- Create a `LogicT` computation from an array of values. -/
def fromArray (xs : Array a) : LogicT r m a :=
  fromList xs.toList

/-- Choose nondeterministically from a list. -/
def choose (xs : List a) : LogicT r m a :=
  fromList xs

/-- The stream type for lazy `msplit` results.

    An `MStream m a` is either empty or a head value `a` paired with a
    monadic action that produces the next `MStream` element when forced.
    This allows `msplit` to be lazy: it only computes up to the first
    result, deferring the rest.

    Uses `unsafe` because `m (MStream m a)` is a non-positive occurrence—
    Lean's kernel rejects it, but it is safe in practice since `m` is always
    covariant. -/
unsafe inductive MStream (m : Type → Type) (a : Type) where
  | nil : MStream m a
  | cons : a → m (MStream m a) → MStream m a

/-- Convert an `MStream` back to a `LogicT` computation.
    Each element is re-injected via `pure`/`<|>`, and the tail is
    forced lazily when the continuation asks for more results. -/
unsafe def MStream.toLogicT [Monad m] : MStream m a → LogicT r m a
  | .nil => failure
  | .cons x rest => (Pure.pure x : LogicT r m a) <|> fun sk fk => do
      let next ← rest
      (MStream.toLogicT next : LogicT r m a) sk fk

end LogicT
