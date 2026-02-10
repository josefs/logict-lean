/-
  LogicT operations: msplit and derived logic programming combinators.
-/
import LogicT.Basic
import LogicT.Class

namespace LogicT

variable {m : Type → Type} {a b : Type}

/-- Run one step of a `LogicT` computation, forcing any monadic effects.
    Returns `none` if no more results, or `some (a, rest)`. -/
unsafe def LogicT.step [Monad m] : LogicT m a → m (Option (a × LogicT m a))
  | .nil => pure none
  | .cons x rest => pure (some (x, rest))
  | .liftM action => action >>= LogicT.step

/-- Split a `LogicT` computation into its first result and the rest.

    This is the key primitive for logic programming. It non-destructively
    decomposes a nondeterministic computation, giving access to the first
    result (if any) and a continuation for the remaining results.

    Laws:
    - `LogicT.msplit failure = pure none`
    - `LogicT.msplit (pure a <|> m) = pure (some (a, m))` -/
unsafe def LogicT.msplit [Monad m] (l : LogicT m a) : m (Option (a × LogicT m a)) :=
  l.step

/-- The inverse of `msplit`. Reconstruct a `LogicT` computation from a split result.

    Satisfies: `LogicT.msplit m >>= LogicT.reflect = m` -/
unsafe def LogicT.reflect [Monad m] : Option (a × LogicT m a) → LogicT m a
  | none => .nil
  | some (a, rest) => .cons a rest

/-- `MonadLogic` instance for `LogicT`. -/
unsafe instance [Monad m] : MonadLogic (LogicT m) where
  msplit l := LogicT.lift l.step

/-- Fair disjunction for `LogicT`. Interleaves results from two computations,
    ensuring both are considered even if one produces infinitely many results.

    Unlike `<|>`, which is depth-first, `interleave` alternates between branches. -/
unsafe def LogicT.interleave [Monad m] (m₁ m₂ : LogicT m a) : LogicT m a :=
  .liftM do
    match ← m₁.step with
    | none => pure m₂
    | some (a, m₁') => pure (.cons a (LogicT.interleave m₂ m₁'))

/-- Fair conjunction for `LogicT`. Like `>>=` but interleaves results
    to ensure fairness when the left computation produces many results.

    This is `>>-` in the Haskell library. -/
unsafe def LogicT.fairBind [Monad m] (ma : LogicT m a) (f : a → LogicT m b) : LogicT m b :=
  .liftM do
    match ← ma.step with
    | none => pure .nil
    | some (a, ma') => pure (LogicT.interleave (f a) (LogicT.fairBind ma' f))

/-- Pruning for `LogicT`. Selects at most one result from a computation.
    Useful when multiple results would be equivalent. -/
unsafe def LogicT.once [Monad m] (ma : LogicT m a) : LogicT m a :=
  .liftM do
    match ← ma.step with
    | none => pure .nil
    | some (a, _) => pure (.cons a .nil)

/-- Logical negation for `LogicT`. Succeeds (with `()`) if the computation
    fails, and fails if the computation succeeds. -/
unsafe def LogicT.lnot [Monad m] (ma : LogicT m a) : LogicT m Unit :=
  .liftM do
    match ← ma.step with
    | none => pure (.cons () .nil)
    | some _ => pure .nil

/-- Logical conditional (soft-cut) for `LogicT`.
    If the first computation succeeds, feed its results to the success
    branch `th`. Otherwise, take the failure branch `el`.

    Laws:
    - `ifte (pure a) th el = th a`
    - `ifte failure th el = el`
    - `ifte (pure a <|> m) th el = th a <|> (m >>= th)` -/
unsafe def LogicT.ifte [Monad m] (t : LogicT m a) (th : a → LogicT m b) (el : LogicT m b)
    : LogicT m b :=
  .liftM do
    match ← t.step with
    | none => pure el
    | some (a, rest) => pure (LogicT.append (th a) (LogicT.bind' rest th))

end LogicT
