/-
  LogicT: A backtracking, logic-programming monad transformer for Lean 4.

  This library provides `LogicT`, a monad transformer for performing
  backtracking computations layered over another monad, and `Logic`,
  the pure specialization equivalent to a lazy list.

  Based on the Haskell `logict` library, adapted from the paper
  "Backtracking, Interleaving, and Terminating Monad Transformers"
  by Oleg Kiselyov, Chung-chieh Shan, Daniel P. Friedman, Amr Sabry.
-/

import LogicT.Basic
import LogicT.Class
import LogicT.Operations
import LogicT.Observation
