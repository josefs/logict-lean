/-
  MonadLogic: The typeclass for backtracking, logic-programming monads.

  Provides the core operations beyond Alternative:
  - `msplit`: decompose a computation into its first result and the rest
  - `interleave`: fair disjunction
  - `fairBind`: fair conjunction (>>- in Haskell)
  - `once`: pruning (take only the first result)
  - `lnot`: logical negation
  - `ifte`: logical conditional (soft-cut)
-/

namespace LogicT

/-- A typeclass for monads supporting backtracking logic programming.

    The key primitive is `msplit`, which decomposes a computation into
    its first result (if any) and a computation representing the rest.
    All other operations can be defined in terms of `msplit`. -/
class MonadLogic (m : Type → Type) [Monad m] [Alternative m] where
  /-- Attempt to split a computation, returning the first result and
      the remaining computation, or `none` if there are no results.

      Laws:
      - `msplit failure = pure none`
      - `msplit (pure a <|> m) = pure (some (a, m))` -/
  msplit {a : Type} : m a → m (Option (a × m a))

variable {m : Type → Type} [Monad m] [Alternative m] [MonadLogic m]
variable {a b : Type}

/-- The inverse of `msplit`. Reconstruct a computation from a split result.

    Satisfies: `msplit m >>= reflect = m` -/
@[inline]
def reflect : Option (a × m a) → m a
  | none => failure
  | some (a, m) => pure a <|> m

/-- Fair disjunction. Interleaves results from two computations,
    ensuring both are considered even if one produces infinitely many results.

    Unlike `<|>`, which is depth-first, `interleave` alternates between
    branches:

    ```
    interleave [1,2,3] [4,5,6] = [1,4,2,5,3,6]
    ``` -/
partial def interleave [Inhabited (m a)] (m₁ m₂ : m a) : m a := do
  match ← MonadLogic.msplit m₁ with
  | none => m₂
  | some (a, m₁') => pure a <|> interleave m₂ m₁'

/-- Fair conjunction. Like monadic bind (`>>=`), but interleaves results
    to ensure fairness when the left computation produces many results.

    This is `>>-` in the Haskell library. -/
partial def fairBind [Inhabited (m b)] (ma : m a) (f : a → m b) : m b := do
  match ← MonadLogic.msplit ma with
  | none => failure
  | some (a, ma') => interleave (f a) (fairBind ma' f)

/-- Pruning. Selects at most one result from a computation.
    Useful when multiple results would be equivalent. -/
def once (ma : m a) : m a := do
  match ← MonadLogic.msplit ma with
  | none => failure
  | some (a, _) => pure a

/-- Logical negation. Succeeds (with `()`) if the computation fails,
    and fails if the computation succeeds. -/
def lnot (ma : m a) : m Unit := do
  match ← MonadLogic.msplit ma with
  | none => pure ()
  | some _ => failure

/-- Logical conditional (soft-cut). If the first computation succeeds,
    feed its results to the success branch. Otherwise, take the failure branch.

    Laws:
    - `ifte (pure a) th el = th a`
    - `ifte failure th el = el`
    - `ifte (pure a <|> m) th el = th a <|> (m >>= th)` -/
def ifte (t : m a) (th : a → m b) (el : m b) : m b := do
  match ← MonadLogic.msplit t with
  | none => el
  | some (a, m) => th a <|> (m >>= th)

end LogicT
