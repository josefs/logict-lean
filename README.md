# LogicT

A backtracking, logic-programming monad transformer for Lean 4.

Based on the Haskell [`logict`](https://hackage.haskell.org/package/logict) library, adapted from the paper [*Backtracking, Interleaving, and Terminating Monad Transformers*](http://okmij.org/ftp/papers/LogicT.pdf) by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, and Amr Sabry.

## ⚠️ Use of `unsafe`

This library uses `unsafe inductive` to define the core `LogicT` type. The type is a lazy stream where the tail can be wrapped in a monadic action (`m (LogicT m a)`), which means `LogicT` appears nested inside the parameter `m`. Lean's strict positivity checker cannot verify that this is safe for an arbitrary `m` (since `m` could in principle be a non-positive functor), so the definition is rejected without `unsafe`. The Haskell library avoids this issue by using a CPS encoding, but in Lean 4 that encoding produces a `Type 1` value, making `msplit` — the key operation of the library — impossible to type at `Type 0`.

All functions that pattern-match on the `LogicT` constructors are also marked `unsafe` as a consequence. The API is safe to use in practice; the unsafety is a limitation of what Lean's type system can express, not an indication of undefined behavior.

## Overview

`LogicT m a` is a monad transformer for nondeterministic computations that can produce zero or more results of type `a`, with effects in `m`. When `m = Id`, the type alias `Logic a` is provided as a convenient shorthand.

### Features

- **Backtracking search** — express nondeterministic computations using `pure`, `Alternative.failure`, and `<|>`
- **Fair operations** — `interleave` (fair disjunction) and `fairBind` (fair conjunction) for search strategies that don't get stuck exploring one branch forever
- **Pruning** — `once` returns only the first result; `lnot` succeeds only when a computation fails
- **Soft-cut** — `ifte` (if-then-else for logic programming) commits to the first branch if it succeeds
- **Observation** — `observeAll`, `observe`, and `observeMany` extract results from computations
- **Monad transformer** — layer logic programming over any monad via `MonadLift`

## Installation

Add to your `lakefile.lean`:

```lean
require logict from git "https://github.com/josefs/logict" @ "main"
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

### Core Type

- `LogicT m a` — a nondeterministic computation with effects in `m`
- `Logic a` — type alias for `LogicT Id a`

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

### MonadLogic Operations

| Function | Description |
|---|---|
| `msplit m` | Split into first result and rest: `m a → m (Option (a × m a))` |
| `interleave a b` | Fair disjunction — alternates results from `a` and `b` |
| `fairBind m f` | Fair conjunction — interleaves results of `f` across choices from `m` |
| `once m` | Prune to at most one result |
| `lnot m` | Succeed with `()` iff `m` fails |
| `ifte cond th el` | If `cond` succeeds, commit to `th` applied to its results; otherwise use `el` |
| `reflect o` | Construct from `Option (a × m a)` (inverse of `msplit`) |

### Observation (Extracting Results)

| Function | Description |
|---|---|
| `observeAllT` | Extract all results: `LogicT m a → m (List a)` |
| `observeT` | Extract first result: `LogicT m a → m (Option a)` |
| `observeManyT n` | Extract up to `n` results: `Nat → LogicT m a → m (List a)` |
| `Logic.observeAll` | `Logic a → List a` |
| `Logic.observe` | `Logic a → Option a` |
| `Logic.observeMany n` | `Nat → Logic a → List a` |

## Modules

- **`LogicT.Basic`** — Core `LogicT` type, `Monad`/`Alternative`/`MonadLift` instances, utility functions
- **`LogicT.Class`** — `MonadLogic` typeclass with generic default implementations
- **`LogicT.Instances`** — `MonadLogic` instance for `LogicT`, specialized operations
- **`LogicT.Observation`** — Functions for extracting results from computations

## Testing

```sh
lake build logict-test && lake exe logict-test
```

## License

MIT — see [LICENSE](LICENSE).
