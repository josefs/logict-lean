/-
  LogicT operations: msplit and derived logic programming combinators.

  `msplit` is implemented lazily using `MStream`: it only computes up to
  the first result, capturing the remaining alternatives as a deferred
  monadic action. All derived operations (`once`, `lnot`, `ifte`,
  `interleave`, `fairBind`) are built on top of `msplit`.

  The `observeAllT` function is provided separately as an efficient
  eager observation that doesn't use `MStream`.
-/
import LogicT.Basic
import LogicT.Class

namespace LogicT

variable {r : Type} {m : Type → Type} {a b : Type}

/-- The split-compatible type for `LogicT`.
    `LogicM m a` is `LogicT` with `r = MStream m a`, allowing the result
    type to co-vary with `a` as needed for lazy `msplit`. -/
unsafe abbrev LogicM (m : Type → Type) (a : Type) : Type :=
  LogicT (MStream m a) m a

/-- The inverse of `msplit`. Reconstruct a `LogicT` computation from a split result.

    Satisfies: `msplit m >>= reflect = m` -/
def reflect : Option (a × LogicT r m a) → LogicT r m a
  | none => failure
  | some (x, rest) => Pure.pure x <|> rest

/-- Extract all results from a `LogicT` computation.

    This is an efficient eager observation that fixes `r = List a`.
    It does not use `MStream` and runs the entire computation.

    Warning: will not terminate if the computation produces infinitely many results. -/
def observeAllT [Monad m] (l : LogicT (List a) m a) : m (List a) :=
  l (fun x rest => do let xs ← rest; pure (x :: xs)) (pure [])

/-- Lazily split a `LogicT` computation into its first result and the rest.

    This is the key primitive for logic programming. Only the first
    alternative is evaluated; the remaining alternatives are captured
    in an `MStream` and deferred until needed.

    Fixes `r = MStream m a`.

    Laws:
    - `msplit failure = pure MStream.nil`
    - `msplit (pure a <|> m) = pure (MStream.cons a (msplit m))` -/
unsafe def msplit [Monad m] (l : LogicT (MStream m a) m a) : m (MStream m a) :=
  l (fun x fk => pure (MStream.cons x fk)) (pure MStream.nil)

/-- Lazily split a `LogicT` computation, returning `Option` for convenience.

    Returns `some (a, rest)` where `rest` is a `LogicT` computation
    representing the remaining alternatives, or `none` if empty. -/
unsafe def msplit' [Monad m] (l : LogicT (MStream m a) m a)
    : m (Option (a × LogicT (MStream m a) m a)) := do
  match ← msplit l with
  | .nil => pure none
  | .cons x rest => pure (some (x, fun sk fk => do
      let next ← rest
      (MStream.toLogicT next : LogicT (MStream m a) m a) sk fk))

/-- Pruning for `LogicT`. Selects at most one result from a computation.
    Only evaluates the first alternative (lazy via `msplit`). -/
unsafe def once [Monad m] (l : LogicT (MStream m a) m a) : LogicT r m a :=
  fun sk fk => do
    match ← msplit l with
    | .nil => fk
    | .cons x _ => sk x fk

/-- Logical negation for `LogicT`. Succeeds (with `()`) if the computation
    fails, and fails if the computation succeeds.
    Only evaluates the first alternative (lazy via `msplit`). -/
unsafe def lnot [Monad m] (l : LogicT (MStream m a) m a) : LogicT r m Unit :=
  fun sk fk => do
    match ← msplit l with
    | .nil => sk () fk
    | .cons _ _ => fk

/-- Logical conditional (soft-cut) for `LogicT`.
    If the first computation succeeds, feed its results to the success
    branch `th`. Otherwise, take the failure branch `el`.

    Uses lazy `msplit` to check whether the test computation has results.

    Laws:
    - `ifte (pure a) th el = th a`
    - `ifte failure th el = el`
    - `ifte (pure a <|> m) th el = th a <|> (m >>= th)` -/
unsafe def ifte [Monad m] (t : LogicT (MStream m a) m a)
    (th : a → LogicT r m b) (el : LogicT r m b) : LogicT r m b :=
  fun sk fk => do
    match ← msplit t with
    | .nil => el sk fk
    | .cons x rest =>
      (th x <|> fun sk' fk' => do
        let tail ← rest
        ((MStream.toLogicT tail : LogicT r m a) >>= th) sk' fk') sk fk

/-- Fair disjunction for `LogicT`. Interleaves results from two computations,
    ensuring both are considered even if one produces infinitely many results.

    Unlike `<|>`, which is depth-first, `interleave` alternates between
    branches. Uses lazy `msplit` internally. -/
unsafe def interleave [Monad m]
    (m₁ m₂ : LogicT (MStream m a) m a) : LogicT (MStream m a) m a :=
  fun sk fk => do
    match ← msplit m₁ with
    | .nil => m₂ sk fk
    | .cons x rest =>
      sk x ((interleave m₂ (fun sk' fk' => do
        let tail ← rest
        (MStream.toLogicT tail : LogicT (MStream m a) m a) sk' fk')) sk fk)

/-- Fair conjunction for `LogicT`. Like `>>=` but interleaves results
    to ensure fairness when the left computation produces many results.

    This is `>>-` in the Haskell library. Uses lazy `msplit` internally. -/
unsafe def fairBind [Monad m]
    (ma : LogicT (MStream m a) m a) (f : a → LogicT (MStream m b) m b)
    : LogicT (MStream m b) m b :=
  fun sk fk => do
    match ← msplit ma with
    | .nil => fk
    | .cons x rest =>
      (interleave (f x) (fairBind (fun sk' fk' => do
        let tail ← rest
        (MStream.toLogicT tail : LogicT (MStream m a) m a) sk' fk') f)) sk fk

/-- `MonadLogic` instance for `LogicT` via `LogicM`. -/
unsafe instance [Monad m] : MonadLogic (LogicM m) m where
  msplit := msplit'
  reflect := reflect
  interp mfa := fun sk fk => do let fa ← mfa; fa sk fk
  append := LogicT.append

end LogicT
