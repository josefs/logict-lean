/-
  Tests for the LogicT library.

  Run with: lake exe logict-test
-/
import LogicT

open LogicT

unsafe def assertEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    IO.println s!"  ✓ {name}"
  else
    IO.eprintln s!"  ✗ {name}: expected {expected}, got {actual}"
    throw <| IO.userError s!"Test failed: {name}"

-- Helper: run a LogicT Id and collect all results
unsafe def allResults {α : Type} (l : LogicT Id α) : List α :=
  Logic.observeAll l

-- Helper: run a LogicT Id and get the first result
unsafe def firstResult {α : Type} (l : LogicT Id α) : Option α :=
  Logic.observe l

-- ============================================================
-- Basic construction and observation
-- ============================================================

unsafe def testBasic : IO Unit := do
  IO.println "Basic construction and observation:"

  -- pure produces a single result
  assertEq "pure"
    (allResults (pure 42 : LogicT Id Nat))
    [42]

  -- failure produces no results
  assertEq "failure"
    (allResults (failure : LogicT Id Nat))
    []

  -- <|> combines results in order
  assertEq "<|>"
    (allResults (pure 1 <|> pure 2 <|> pure 3 : LogicT Id Nat))
    [1, 2, 3]

  -- fromList
  assertEq "fromList"
    (allResults (LogicT.fromList [10, 20, 30] : LogicT Id Nat))
    [10, 20, 30]

  -- fromList empty
  assertEq "fromList []"
    (allResults (LogicT.fromList ([] : List Nat) : LogicT Id Nat))
    []

  -- fromArray
  assertEq "fromArray"
    (allResults (LogicT.fromArray #[4, 5, 6] : LogicT Id Nat))
    [4, 5, 6]

-- ============================================================
-- Observation variants
-- ============================================================

unsafe def testObservation : IO Unit := do
  IO.println "Observation variants:"

  let l : LogicT Id Nat := pure 5 <|> pure 3 <|> pure 7

  -- observeAll
  assertEq "observeAll"
    (Logic.observeAll l)
    [5, 3, 7]

  -- observe (first result)
  assertEq "observe some"
    (Logic.observe l)
    (some 5)

  -- observe on empty
  assertEq "observe none"
    (Logic.observe (failure : LogicT Id Nat))
    (none : Option Nat)

  -- observeMany
  assertEq "observeMany 2"
    (Logic.observeMany 2 l)
    [5, 3]

  assertEq "observeMany 0"
    (Logic.observeMany 0 l)
    ([] : List Nat)

  assertEq "observeMany 10 (more than available)"
    (Logic.observeMany 10 l)
    [5, 3, 7]

-- ============================================================
-- Monad instance (bind / do-notation)
-- ============================================================

unsafe def testMonad : IO Unit := do
  IO.println "Monad instance:"

  -- bind distributes over alternatives
  let l : LogicT Id Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    let y ← pure 10 <|> pure 20
    pure (x + y)
  assertEq "bind distributes"
    (allResults l)
    [11, 21, 12, 22, 13, 23]

  -- bind with failure prunes branches
  let l2 : LogicT Id Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    if x == 2 then failure else pure (x * 10)
  assertEq "bind with failure"
    (allResults l2)
    [10, 30]

  -- map (Functor)
  let l3 : LogicT Id Nat := (· + 100) <$> (pure 1 <|> pure 2)
  assertEq "map"
    (allResults l3)
    [101, 102]

  -- nested bind
  let l4 : LogicT Id Nat := do
    let x ← pure 1 <|> pure 2
    let y ← pure 10 <|> pure 20
    let z ← pure 100 <|> pure 200
    pure (x + y + z)
  assertEq "nested bind"
    (allResults l4)
    [111, 211, 121, 221, 112, 212, 122, 222]

-- ============================================================
-- Guard
-- ============================================================

unsafe def testGuard : IO Unit := do
  IO.println "Guard:"

  -- guard keeps only even numbers
  let l : LogicT Id Nat := do
    let x ← LogicT.fromList [1, 2, 3, 4, 5, 6]
    LogicT.guard (x % 2 == 0)
    pure x
  assertEq "guard even"
    (allResults l)
    [2, 4, 6]

  -- guard false produces nothing
  assertEq "guard false"
    (allResults (LogicT.guard (m := Id) false))
    ([] : List Unit)

  -- guard true produces unit
  assertEq "guard true"
    (allResults (LogicT.guard (m := Id) true))
    [()]

-- ============================================================
-- msplit
-- ============================================================

unsafe def testMsplit : IO Unit := do
  IO.println "msplit:"

  -- msplit on non-empty
  let r1 : Option (Nat × LogicT Id Nat) :=
    LogicT.msplit (pure 1 <|> pure 2 <|> pure 3 : LogicT Id Nat)
  match r1 with
  | some (x, rest) =>
    assertEq "msplit head" x 1
    assertEq "msplit rest" (allResults rest) [2, 3]
  | none => throw <| IO.userError "msplit returned none unexpectedly"

  -- msplit on empty
  let r2 : Option (Nat × LogicT Id Nat) :=
    LogicT.msplit (failure : LogicT Id Nat)
  assertEq "msplit empty" r2.isNone true

  -- msplit on single
  let r3 : Option (Nat × LogicT Id Nat) :=
    LogicT.msplit (pure 42 : LogicT Id Nat)
  match r3 with
  | some (x, rest) =>
    assertEq "msplit single head" x 42
    assertEq "msplit single rest" (allResults rest) ([] : List Nat)
  | none => throw <| IO.userError "msplit single returned none"

-- ============================================================
-- reflect
-- ============================================================

unsafe def testReflect : IO Unit := do
  IO.println "reflect:"

  -- reflect none = failure
  assertEq "reflect none"
    (allResults (LogicT.reflect (none : Option (Nat × LogicT Id Nat))))
    ([] : List Nat)

  -- reflect some reconstructs
  let rest : LogicT Id Nat := pure 2 <|> pure 3
  assertEq "reflect some"
    (allResults (LogicT.reflect (some (1, rest))))
    [1, 2, 3]

-- ============================================================
-- interleave (fair disjunction)
-- ============================================================

unsafe def testInterleave : IO Unit := do
  IO.println "interleave (fair disjunction):"

  let l1 : LogicT Id Nat := pure 1 <|> pure 2 <|> pure 3
  let l2 : LogicT Id Nat := pure 4 <|> pure 5 <|> pure 6

  -- interleave alternates
  assertEq "interleave"
    (allResults (LogicT.interleave l1 l2))
    [1, 4, 2, 5, 3, 6]

  -- interleave with empty left
  assertEq "interleave empty left"
    (allResults (LogicT.interleave failure l2))
    [4, 5, 6]

  -- interleave with empty right
  assertEq "interleave empty right"
    (allResults (LogicT.interleave l1 failure))
    [1, 2, 3]

  -- interleave both empty
  assertEq "interleave both empty"
    (allResults (LogicT.interleave (failure : LogicT Id Nat) failure))
    ([] : List Nat)

  -- interleave unequal lengths
  let short : LogicT Id Nat := pure 10
  let long : LogicT Id Nat := pure 20 <|> pure 30 <|> pure 40
  assertEq "interleave unequal"
    (allResults (LogicT.interleave short long))
    [10, 20, 30, 40]

-- ============================================================
-- fairBind (fair conjunction, >>-)
-- ============================================================

unsafe def testFairBind : IO Unit := do
  IO.println "fairBind (fair conjunction):"

  -- Compare depth-first bind vs fair bind
  let sources : LogicT Id Nat := LogicT.fromList [100, 200]
  let expand (x : Nat) : LogicT Id Nat :=
    LogicT.fromList [x + 1, x + 2, x + 3]

  -- depth-first: all of 100's results before 200's
  assertEq "bind depth-first"
    (allResults (sources >>= expand))
    [101, 102, 103, 201, 202, 203]

  -- fair: interleaved
  assertEq "fairBind interleaved"
    (allResults (LogicT.fairBind sources expand))
    [101, 201, 102, 202, 103, 203]

  -- fairBind with single source
  assertEq "fairBind single source"
    (allResults (LogicT.fairBind (pure 10 : LogicT Id Nat) (fun x => pure (x + 1))))
    [11]

  -- fairBind with empty source
  assertEq "fairBind empty source"
    (allResults (LogicT.fairBind (failure : LogicT Id Nat) (fun x => pure (x + 1))))
    ([] : List Nat)

-- ============================================================
-- once (pruning)
-- ============================================================

unsafe def testOnce : IO Unit := do
  IO.println "once (pruning):"

  assertEq "once multiple"
    (allResults (LogicT.once (pure 1 <|> pure 2 <|> pure 3 : LogicT Id Nat)))
    [1]

  assertEq "once single"
    (allResults (LogicT.once (pure 42 : LogicT Id Nat)))
    [42]

  assertEq "once empty"
    (allResults (LogicT.once (failure : LogicT Id Nat)))
    ([] : List Nat)

-- ============================================================
-- lnot (logical negation)
-- ============================================================

unsafe def testLnot : IO Unit := do
  IO.println "lnot (logical negation):"

  -- lnot of failure succeeds
  assertEq "lnot failure"
    (allResults (LogicT.lnot (failure : LogicT Id Nat)))
    [()]

  -- lnot of success fails
  assertEq "lnot success"
    (allResults (LogicT.lnot (pure 1 : LogicT Id Nat)))
    ([] : List Unit)

  -- lnot of multiple successes fails
  assertEq "lnot multiple"
    (allResults (LogicT.lnot (pure 1 <|> pure 2 : LogicT Id Nat)))
    ([] : List Unit)

-- ============================================================
-- ifte (soft-cut / logical conditional)
-- ============================================================

unsafe def testIfte : IO Unit := do
  IO.println "ifte (soft-cut):"

  -- ifte success: applies th to all results
  assertEq "ifte success"
    (allResults (LogicT.ifte (pure 1 <|> pure 2 : LogicT Id Nat)
        (fun x => pure (x * 10))
        (pure 0)))
    [10, 20]

  -- ifte failure: takes el branch
  assertEq "ifte failure"
    (allResults (LogicT.ifte (failure : LogicT Id Nat)
        (fun x => pure (x * 10))
        (pure 0)))
    [0]

  -- ifte single: applies th
  assertEq "ifte single"
    (allResults (LogicT.ifte (pure 5 : LogicT Id Nat)
        (fun x => pure (x + 1))
        (pure 0)))
    [6]

-- ============================================================
-- Logic programming examples
-- ============================================================

unsafe def testExamples : IO Unit := do
  IO.println "Logic programming examples:"

  -- Grandparent example (from the Haskell logict README)
  let parents : List (String × String) :=
    [("Sarah", "John"), ("Arnold", "John"), ("John", "Anne")]

  let grandparent (grandchild : String) : LogicT Id String := do
    let (p, c) ← LogicT.fromList parents
    let (c', g) ← LogicT.fromList parents
    LogicT.guard (c == c')
    LogicT.guard (g == grandchild)
    pure p

  assertEq "grandparent Anne"
    (allResults (grandparent "Anne"))
    ["Sarah", "Arnold"]

  assertEq "grandparent John (none)"
    (allResults (grandparent "John"))
    ([] : List String)

  -- Pythagorean triples
  let triples (n : Nat) : LogicT Id (Nat × Nat × Nat) := do
    let a ← LogicT.fromList (List.range n |>.map (· + 1))
    let b ← LogicT.fromList (List.range n |>.map (· + 1))
    let c ← LogicT.fromList (List.range n |>.map (· + 1))
    LogicT.guard (a * a + b * b == c * c)
    LogicT.guard (a ≤ b)  -- avoid duplicates
    pure (a, b, c)

  assertEq "pythagorean triples ≤ 15"
    (allResults (triples 15))
    [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]

  -- Composite number check using once
  let divisors (n : Nat) : LogicT Id (Nat × Nat) := do
    let a ← LogicT.fromList (List.range (n - 2) |>.map (· + 2))
    let b ← LogicT.fromList (List.range (n - 2) |>.map (· + 2))
    LogicT.guard (a * b == n)
    pure (a, b)

  let isComposite (n : Nat) : Bool :=
    (LogicT.once (divisors n)).observeT |>.isSome

  assertEq "20 is composite" (isComposite 20) true
  assertEq "7 is not composite" (isComposite 7) false
  assertEq "12 is composite" (isComposite 12) true

  -- Prime check using lnot
  let isPrime (n : Nat) : Bool :=
    n > 1 && ((do
      let _ ← LogicT.lnot (divisors n)
      pure true : LogicT Id Bool).observeT |>.getD false)

  assertEq "7 is prime" (isPrime 7) true
  assertEq "20 is not prime" (isPrime 20) false
  assertEq "2 is prime" (isPrime 2) true
  assertEq "1 is not prime" (isPrime 1) false

-- ============================================================
-- MonadLift (transformer behavior)
-- ============================================================

unsafe def testMonadLift : IO Unit := do
  IO.println "MonadLift (transformer):"

  -- Lift IO into LogicT
  let l : LogicT IO Nat := do
    let x ← pure 1 <|> pure 2
    let y : Nat ← MonadLift.monadLift (pure 10 : IO Nat)
    pure (x + y)
  let result ← l.observeAllT
  assertEq "lift IO" result [11, 12]

  -- Multiple lifted effects
  let ref ← IO.mkRef (0 : Nat)
  let l2 : LogicT IO Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    MonadLift.monadLift (ref.modify (· + 1) : IO Unit)
    pure x
  let results ← l2.observeAllT
  let count ← ref.get
  assertEq "lift IO effects results" results [1, 2, 3]
  assertEq "lift IO effects count" count 3

-- ============================================================
-- Main
-- ============================================================

unsafe def main : IO Unit := do
  testBasic
  testObservation
  testMonad
  testGuard
  testMsplit
  testReflect
  testInterleave
  testFairBind
  testOnce
  testLnot
  testIfte
  testExamples
  testMonadLift
  IO.println "\nAll tests passed! ✓"
