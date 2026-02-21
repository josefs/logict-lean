# LogicT

A backtracking, logic-programming monad transformer for Lean 4.

Based on the Haskell [`logict`](https://hackage.haskell.org/package/logict) library, adapted from the paper [*Backtracking, Interleaving, and Terminating Monad Transformers*](http://okmij.org/ftp/papers/LogicT.pdf) by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, and Amr Sabry.

## Overview

`LogicT r m a` is a monad transformer for nondeterministic computations that can produce zero or more results of type `a`, with effects in `m`. The parameter `r` is the result type used in the CPS representation; observation functions fix it to a concrete type (e.g. `List a` for `observeAllT`). When `m = Id`, the type alias `Logic a` is provided as a convenient shorthand.

### Features

- **Backtracking search** — express nondeterministic computations using `pure`, `Alternative.failure`, and `<|>`
- **Lazy splitting** — `msplit` decomposes a computation into its first result and the rest, computing only on demand
- **Fair operations** — `interleave` (fair disjunction) and `fairBind` (fair conjunction) for search strategies that don't get stuck exploring one branch forever
- **Pruning** — `once` returns only the first result; `lnot` succeeds only when a computation fails
- **Soft-cut** — `ifte` (if-then-else for logic programming) commits to the first branch if it succeeds
- **Observation** — `observeAll`, `observe`, and `observeMany` extract results from computations
- **Monad transformer** — layer logic programming over any monad via `MonadLift`
- **MonadLogic typeclass** — generic interface for logic-programming monads, with a `LogicT` instance

## Design

### CPS Representation

The core type uses continuation-passing style:

```
LogicT r m a = (a → m r → m r) → m r → m r
```

This representation is safe and does not require `unsafe`. The `r` parameter is fixed by each observation or operation:

- `observeAllT` fixes `r = List a` for efficient eager collection
- `msplit` fixes `r = MStream m a` for lazy splitting
- `once`, `lnot`, etc. accept `r = MStream m a` input and produce output polymorphic in `r`

### Lazy msplit via MStream

The `msplit` function is implemented lazily using `MStream`, a stream type where each tail is a deferred monadic action. When you split a computation, only the first alternative is evaluated; the rest are captured as a suspended `m (MStream m a)` and forced only when needed.

### Use of `unsafe`

The `MStream` type is defined as an `unsafe inductive`:

```lean
unsafe inductive MStream (m : Type → Type) (a : Type) where
  | nil : MStream m a
  | cons : a → m (MStream m a) → MStream m a
```

The `unsafe` is required because `m (MStream m a)` is a non-positive occurrence — `MStream` appears nested inside the parameter `m`. Lean's kernel cannot verify this is safe for an arbitrary `m` (since `m` could in principle be contravariant), so it rejects the definition without `unsafe`. In practice this is safe because `m` is always covariant (a monad).

The core `LogicT` type and its `Monad`/`Alternative`/`MonadLift` instances are entirely safe — no `unsafe` involved. Only `MStream` and functions that pattern-match on it (`msplit`, `once`, `lnot`, `ifte`, `interleave`, `fairBind`) carry the `unsafe` marker. The eager observation function `observeAllT` does not use `MStream` and is also safe.

### MonadLogic Typeclass

The `MonadLogic f m` typeclass provides a generic interface for logic-programming monads. It is parameterized by `f` (the splittable computation type) and `m` (the base monad). The `LogicT` instance uses `LogicM m` as `f`, where `LogicM m a = LogicT (MStream m a) m a` — this lets the result type `r` co-vary with `a` as required by `msplit`.

## Installation

Add to your `lakefile.lean`:

```lean
require logict from git "https://github.com/josefs/logict-lean" @ "main"
```

Then run `lake update`.

## Quick Start

```lean
import LogicT

open LogicT

-- A simple nondeterministic computation
def choices : Logic Nat :=
  pure 1 <|> pure 2 <|> pure 3

-- Filter with guard
def evens : Logic Nat := do
  let x ← choices
  LogicT.guard (x % 2 == 0)
  pure x

#eval! Logic.observeAll evens
-- [2]

-- Pythagorean triples
def pyTriples (n : Nat) : Logic (Nat × Nat × Nat) := do
  let a ← LogicT.choose (List.range (n - 1) |>.map (· + 1))
  let b ← LogicT.choose (List.range (n - a) |>.map (· + a))
  let c ← LogicT.choose (List.range (n - b) |>.map (· + b))
  LogicT.guard (a * a + b * b == c * c)
  pure (a, b, c)

#eval! Logic.observeAll (pyTriples 15)
-- [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]
```

## API Reference

### Core Types

| Type | Description |
|---|---|
| `LogicT r m a` | Nondeterministic computation with effects in `m` and CPS result type `r` |
| `LogicM m a` | `LogicT (MStream m a) m a` — the split-compatible specialization |
| `Logic a` | `LogicT (List a) Id a` — pure logic computations |
| `MStream m a` | Lazy stream for `msplit` results (unsafe inductive) |

### Construction

| Function | Description |
|---|---|
| `pure a` | A single result |
| `Alternative.failure` | No results |
| `a <\|> b` | Combine two computations |
| `LogicT.fromList xs` | Create from a list |
| `LogicT.fromArray xs` | Create from an array |
| `LogicT.choose xs` | Alias for `fromList` |
| `LogicT.guard p` | Fail unless `p` is true |

### Splitting and Reconstruction

| Function | Description |
|---|---|
| `LogicT.msplit l` | Lazily split into first result + deferred rest: returns `m (MStream m a)` |
| `LogicT.msplit' l` | Like `msplit` but returns `m (Option (a × LogicM m a))` |
| `LogicT.reflect o` | Reconstruct from `Option (a × LogicT r m a)` (inverse of split) |

### Logic Operations

| Function | Description |
|---|---|
| `LogicT.interleave a b` | Fair disjunction — alternates results from `a` and `b` |
| `LogicT.fairBind m f` | Fair conjunction — interleaves results of `f` across choices from `m` |
| `LogicT.once m` | Prune to at most one result |
| `LogicT.lnot m` | Succeed with `()` iff `m` fails |
| `LogicT.ifte cond th el` | If `cond` succeeds, apply `th` to its results; otherwise use `el` |

### Observation (Extracting Results)

| Function | Description |
|---|---|
| `LogicT.observeAllT` | Extract all results: `LogicT (List a) m a → m (List a)` |
| `LogicT.observeT` | Extract first result: `LogicT (Option a) m a → m (Option a)` |
| `LogicT.observeManyT n` | Extract up to `n` results |
| `Logic.observeAll` | `Logic a → List a` |
| `Logic.observe` | `Logic a → Option a` |
| `Logic.observeMany n` | `Nat → Logic a → List a` |

### MonadLogic Typeclass

| Method | Description |
|---|---|
| `MonadLogic.msplit` | Split a computation: `f a → m (Option (a × f a))` |
| `MonadLogic.reflect` | Reconstruct from split result |
| `MonadLogic.once` | Prune to first result |
| `MonadLogic.lnot` | Logical negation |
| `MonadLogic.interleave` | Fair disjunction |
| `MonadLogic.fairBind` | Fair conjunction |
| `MonadLogic.ifte` | Soft-cut / logical conditional |
| `MonadLogic.flatMap` | Cross-type bind via repeated splitting |

## Modules

- **`LogicT.Basic`** — Core `LogicT` type, `Monad`/`Alternative`/`MonadLift` instances, `MStream` type, utility functions
- **`LogicT.Class`** — `MonadLogic` typeclass with generic derived operations
- **`LogicT.Operations`** — `LogicM` type alias, concrete `msplit`/`once`/`lnot`/`ifte`/`interleave`/`fairBind`, `MonadLogic` instance for `LogicT`
- **`LogicT.Observation`** — Functions for extracting results from computations, `Logic` type alias

## Testing

```sh
lake test
```

## License

MIT — see [LICENSE](LICENSE).
