/-
  MonadLogic: The typeclass for backtracking, logic-programming monads.

  Provides the core splitting primitive `msplit` and several derived
  operations for logic programming.

  `f` is the type constructor for splittable computations and `m` is
  the base monad. For `LogicT`, the instance uses `LogicM m` as `f`,
  where `LogicM m a = LogicT (MStream m a) m a`.
-/

namespace LogicT

/-- A typeclass for types supporting backtracking logic programming via splitting.

    The key primitive is `msplit`, which decomposes a computation into
    its first result (if any) and a computation representing the rest.
    All other operations can be defined in terms of `msplit`.

    `f` is the type constructor for splittable computations.
    `m` is the base monad used for effects.
    For `LogicT`, the instance uses `LogicM m` as `f`,
    where `LogicM m a = LogicT (MStream m a) m a`. -/
class MonadLogic (f : Type → Type) (m : Type → Type) [Monad m] where
  /-- Lazily split a computation into its first result and the rest.
      Returns `none` if the computation has no results. -/
  msplit {a : Type} : f a → m (Option (a × f a))
  /-- Reconstruct a computation from a split result. Inverse of `msplit`. -/
  reflect {a : Type} : Option (a × f a) → f a
  /-- Embed a monadic computation producing an `f a` into `f a`. -/
  interp {a : Type} : m (f a) → f a
  /-- Concatenate two computations: results from the first, then the second. -/
  append {a : Type} : f a → f a → f a

namespace MonadLogic

variable {f : Type → Type} {m : Type → Type} [Monad m] [inst : MonadLogic f m]
variable {a b : Type}

/-- Pruning. Selects at most one result from a computation.
    Useful when multiple results would be equivalent. -/
def once (l : f a) : f a :=
  inst.interp do
    match ← inst.msplit l with
    | none => pure (inst.reflect none)
    | some (x, _) => pure (inst.reflect (some (x, inst.reflect none)))

/-- Logical negation. Succeeds (with `()`) if the computation fails,
    and fails if the computation succeeds. -/
def lnot (l : f a) : f Unit :=
  inst.interp do
    match ← inst.msplit l with
    | none => pure (inst.reflect (some ((), inst.reflect none)))
    | some _ => pure (inst.reflect none)

/-- Fair disjunction. Interleaves results from two computations,
    ensuring both are considered even if one produces infinitely many results.

    Unlike `append`, which is depth-first, `interleave` alternates between
    branches. -/
partial def interleave [Inhabited (f a)] (l₁ l₂ : f a) : f a :=
  inst.interp do
    match ← inst.msplit l₁ with
    | none => pure l₂
    | some (x, rest) => pure (inst.reflect (some (x, interleave l₂ rest)))

/-- Cross-type bind via repeated splitting. Applies `g` to each result
    of `l` and concatenates all the results.

    Like monadic bind for `f`, but works across different element types
    even when `f` is not a monad. -/
partial def flatMap [Inhabited (f b)] (l : f a) (g : a → f b) : f b :=
  inst.interp do
    match ← inst.msplit l with
    | none => pure (inst.reflect none)
    | some (x, rest) => pure (inst.append (g x) (flatMap rest g))

/-- Logical conditional (soft-cut). If `t` succeeds, feed all its results
    to `th`. Otherwise, take the failure branch `el`.

    Laws:
    - `ifte (reflect (some (a, m))) th el = append (th a) (flatMap m th)`
    - `ifte (reflect none) th el = el` -/
partial def ifte [inh : Inhabited (f b)] (t : f a) (th : a → f b) (el : f b) : f b :=
  inst.interp do
    match ← inst.msplit t with
    | none => pure el
    | some (x, rest) =>
      pure (inst.append (th x) (@flatMap f m _ inst a b inh rest th))

/-- Fair conjunction. Like `flatMap` but interleaves results to ensure
    fairness when the left computation produces many results. -/
partial def fairBind [inh : Inhabited (f b)] (l : f a) (g : a → f b) : f b :=
  inst.interp do
    match ← inst.msplit l with
    | none => pure (inst.reflect none)
    | some (x, rest) =>
      pure (@interleave f m _ inst b inh (g x) (fairBind rest g))

end MonadLogic

end LogicT
