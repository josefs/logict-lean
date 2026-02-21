/-
  Tests for the LogicT library.

  Run with: lake exe logict-test
-/
import LogicT

open LogicT

def assertEq {α : Type} [BEq α] [ToString α] (name : String) (actual expected : α) : IO Unit := do
  if actual == expected then
    IO.println s!"  ✓ {name}"
  else
    IO.eprintln s!"  ✗ {name}: expected {expected}, got {actual}"
    throw <| IO.userError s!"Test failed: {name}"

-- Helper: run a LogicT Id computation and collect all results
def allResults {α : Type} (l : LogicT (List α) Id α) : List α :=
  LogicT.observeAllT l

-- Helper: run a LogicT Id computation and get the first result
def firstResult {α : Type} (l : LogicT (List α) Id α) : Option α :=
  match LogicT.observeAllT l with
  | [] => none
  | x :: _ => some x

-- Helper: run a LogicT Id computation and get up to n results
def someResults {α : Type} (n : Nat) (l : LogicT (List α) Id α) : List α :=
  (LogicT.observeAllT l).take n

-- ============================================================
-- Basic construction and observation
-- ============================================================

def testBasic : IO Unit := do
  IO.println "Basic construction and observation:"

  -- pure produces a single result
  assertEq "pure"
    (allResults (pure 42 : LogicT (List Nat) Id Nat))
    [42]

  -- failure produces no results
  assertEq "failure"
    (allResults (failure : LogicT (List Nat) Id Nat))
    []

  -- <|> combines results in order
  assertEq "<|>"
    (allResults (pure 1 <|> pure 2 <|> pure 3 : LogicT (List Nat) Id Nat))
    [1, 2, 3]

  -- fromList
  assertEq "fromList"
    (allResults (LogicT.fromList [10, 20, 30] : LogicT (List Nat) Id Nat))
    [10, 20, 30]

  -- fromList empty
  assertEq "fromList []"
    (allResults (LogicT.fromList ([] : List Nat) : LogicT (List Nat) Id Nat))
    []

  -- fromArray
  assertEq "fromArray"
    (allResults (LogicT.fromArray #[4, 5, 6] : LogicT (List Nat) Id Nat))
    [4, 5, 6]

-- ============================================================
-- Observation variants
-- ============================================================

def testObservation : IO Unit := do
  IO.println "Observation variants:"

  let l : LogicT (List Nat) Id Nat := pure 5 <|> pure 3 <|> pure 7

  -- observeAll
  assertEq "observeAll"
    (allResults l)
    [5, 3, 7]

  -- observe (first result)
  assertEq "observe some"
    (firstResult l)
    (some 5)

  -- observe on empty
  assertEq "observe none"
    (firstResult (failure : LogicT (List Nat) Id Nat))
    (none : Option Nat)

  -- observeMany
  assertEq "observeMany 2"
    (someResults 2 l)
    [5, 3]

  assertEq "observeMany 0"
    (someResults 0 l)
    ([] : List Nat)

  assertEq "observeMany 10 (more than available)"
    (someResults 10 l)
    [5, 3, 7]

-- ============================================================
-- Monad instance (bind / do-notation)
-- ============================================================

def testMonad : IO Unit := do
  IO.println "Monad instance:"

  -- bind distributes over alternatives
  let l : LogicT (List Nat) Id Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    let y ← pure 10 <|> pure 20
    pure (x + y)
  assertEq "bind distributes"
    (allResults l)
    [11, 21, 12, 22, 13, 23]

  -- bind with failure prunes branches
  let l2 : LogicT (List Nat) Id Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    if x == 2 then failure else pure (x * 10)
  assertEq "bind with failure"
    (allResults l2)
    [10, 30]

  -- map (Functor)
  let l3 : LogicT (List Nat) Id Nat := (· + 100) <$> (pure 1 <|> pure 2)
  assertEq "map"
    (allResults l3)
    [101, 102]

  -- nested bind
  let l4 : LogicT (List Nat) Id Nat := do
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

def testGuard : IO Unit := do
  IO.println "Guard:"

  -- guard keeps only even numbers
  let l : LogicT (List Nat) Id Nat := do
    let x ← LogicT.fromList [1, 2, 3, 4, 5, 6]
    LogicT.guard (x % 2 == 0)
    pure x
  assertEq "guard even"
    (allResults l)
    [2, 4, 6]

  -- guard false produces nothing
  assertEq "guard false"
    (allResults (LogicT.guard (m := Id) (r := List Unit) false))
    ([] : List Unit)

  -- guard true produces unit
  assertEq "guard true"
    (allResults (LogicT.guard (m := Id) (r := List Unit) true))
    [()]

-- ============================================================
-- msplit (lazy)
-- ============================================================

-- Helper to collect all results from an MStream (for testing)
unsafe def streamToList {m : Type → Type} {a : Type} [Monad m] (s : MStream m a) : m (List a) :=
  match s with
  | .nil => pure []
  | .cons x rest => do
      let tail ← rest
      let xs ← streamToList tail
      pure (x :: xs)

unsafe def testMsplit : IO Unit := do
  IO.println "msplit:"

  -- msplit on non-empty (lazy: only computes first result)
  let s1 : MStream Id Nat :=
    LogicT.msplit (pure 1 <|> pure 2 <|> pure 3 : LogicT (MStream Id Nat) Id Nat)
  match s1 with
  | .nil => throw <| IO.userError "msplit returned nil unexpectedly"
  | .cons x rest =>
    assertEq "msplit head" x 1
    assertEq "msplit rest" (Id.run (streamToList (Id.run rest))) [2, 3]

  -- msplit on empty
  let s2 : MStream Id Nat :=
    LogicT.msplit (failure : LogicT (MStream Id Nat) Id Nat)
  match s2 with
  | .nil => assertEq "msplit empty" true true
  | .cons _ _ => throw <| IO.userError "msplit should return nil"

  -- msplit on single
  let s3 : MStream Id Nat :=
    LogicT.msplit (pure 42 : LogicT (MStream Id Nat) Id Nat)
  match s3 with
  | .nil => throw <| IO.userError "msplit single returned nil"
  | .cons x rest =>
    assertEq "msplit single head" x 42
    assertEq "msplit single rest" (Id.run (streamToList (Id.run rest))) ([] : List Nat)

-- ============================================================
-- reflect
-- ============================================================

def testReflect : IO Unit := do
  IO.println "reflect:"

  -- reflect none = failure
  assertEq "reflect none"
    (allResults (LogicT.reflect (none : Option (Nat × LogicT (List Nat) Id Nat))))
    ([] : List Nat)

  -- reflect some reconstructs
  let rest : LogicT (List Nat) Id Nat := pure 2 <|> pure 3
  assertEq "reflect some"
    (allResults (LogicT.reflect (some (1, rest))))
    [1, 2, 3]

-- ============================================================
-- interleave (fair disjunction, lazy via msplit)
-- ============================================================

unsafe def testInterleave : IO Unit := do
  IO.println "interleave (fair disjunction):"

  -- Helper: observe all results from an MStream-typed LogicT computation
  let observeMS (l : LogicT (MStream Id Nat) Id Nat) : List Nat :=
    Id.run (streamToList (LogicT.msplit l : MStream Id Nat))

  -- interleave alternates
  let il := LogicT.interleave
    (pure 1 <|> pure 2 <|> pure 3 : LogicT (MStream Id Nat) Id Nat)
    (pure 4 <|> pure 5 <|> pure 6)
  assertEq "interleave"
    (observeMS il)
    [1, 4, 2, 5, 3, 6]

  -- interleave with empty left
  assertEq "interleave empty left"
    (observeMS (LogicT.interleave failure (pure 4 <|> pure 5 <|> pure 6)))
    [4, 5, 6]

  -- interleave with empty right
  assertEq "interleave empty right"
    (observeMS (LogicT.interleave (pure 1 <|> pure 2 <|> pure 3) failure))
    [1, 2, 3]

  -- interleave both empty
  assertEq "interleave both empty"
    (observeMS (LogicT.interleave
      (failure : LogicT (MStream Id Nat) Id Nat) failure))
    ([] : List Nat)

  -- interleave unequal lengths
  assertEq "interleave unequal"
    (observeMS (LogicT.interleave
      (pure 10 : LogicT (MStream Id Nat) Id Nat)
      (pure 20 <|> pure 30 <|> pure 40)))
    [10, 20, 30, 40]

-- ============================================================
-- fairBind (fair conjunction, >>-, lazy via msplit)
-- ============================================================

unsafe def testFairBind : IO Unit := do
  IO.println "fairBind (fair conjunction):"

  let observeMS (l : LogicT (MStream Id Nat) Id Nat) : List Nat :=
    Id.run (streamToList (LogicT.msplit l : MStream Id Nat))

  -- Compare depth-first bind vs fair bind
  let sources : LogicT (List Nat) Id Nat := LogicT.fromList [100, 200]
  let expand (x : Nat) : LogicT (List Nat) Id Nat :=
    LogicT.fromList [x + 1, x + 2, x + 3]

  -- depth-first: all of 100's results before 200's
  assertEq "bind depth-first"
    (allResults (sources >>= expand))
    [101, 102, 103, 201, 202, 203]

  -- fair: interleaved
  let fbResult := LogicT.fairBind
    (LogicT.fromList [100, 200] : LogicT (MStream Id Nat) Id Nat)
    (fun x => LogicT.fromList [x + 1, x + 2, x + 3])
  assertEq "fairBind interleaved"
    (observeMS fbResult)
    [101, 201, 102, 202, 103, 203]

  -- fairBind with single source
  assertEq "fairBind single source"
    (observeMS (LogicT.fairBind
      (pure 10 : LogicT (MStream Id Nat) Id Nat)
      (fun x => pure (x + 1))))
    [11]

  -- fairBind with empty source
  assertEq "fairBind empty source"
    (observeMS (LogicT.fairBind
      (failure : LogicT (MStream Id Nat) Id Nat)
      (fun x => pure (x + 1))))
    ([] : List Nat)

-- ============================================================
-- once (pruning, lazy via msplit)
-- ============================================================

unsafe def testOnce : IO Unit := do
  IO.println "once (pruning):"

  -- once: output r is polymorphic, so allResults (r=List) works directly
  assertEq "once multiple"
    (allResults (LogicT.once (pure 1 <|> pure 2 <|> pure 3
      : LogicT (MStream Id Nat) Id Nat)))
    [1]

  assertEq "once single"
    (allResults (LogicT.once (pure 42 : LogicT (MStream Id Nat) Id Nat)))
    [42]

  assertEq "once empty"
    (allResults (LogicT.once (failure : LogicT (MStream Id Nat) Id Nat)))
    ([] : List Nat)

-- ============================================================
-- lnot (logical negation, lazy via msplit)
-- ============================================================

unsafe def testLnot : IO Unit := do
  IO.println "lnot (logical negation):"

  -- lnot of failure succeeds (output r is polymorphic)
  let r1 : List Unit := LogicT.observeAllT
    (LogicT.lnot (failure : LogicT (MStream Id Nat) Id Nat))
  assertEq "lnot failure" r1 [()]

  -- lnot of success fails
  let r2 : List Unit := LogicT.observeAllT
    (LogicT.lnot (pure 1 : LogicT (MStream Id Nat) Id Nat))
  assertEq "lnot success" r2 ([] : List Unit)

  -- lnot of multiple successes fails (only checks first - lazy!)
  let r3 : List Unit := LogicT.observeAllT
    (LogicT.lnot (pure 1 <|> pure 2 : LogicT (MStream Id Nat) Id Nat))
  assertEq "lnot multiple" r3 ([] : List Unit)

-- ============================================================
-- ifte (soft-cut / logical conditional, lazy via msplit)
-- ============================================================

unsafe def testIfte : IO Unit := do
  IO.println "ifte (soft-cut):"

  -- ifte success: applies th to all results
  assertEq "ifte success"
    (allResults (LogicT.ifte
        (pure 1 <|> pure 2 : LogicT (MStream Id Nat) Id Nat)
        (fun x => pure (x * 10))
        (pure 0)))
    [10, 20]

  -- ifte failure: takes el branch
  assertEq "ifte failure"
    (allResults (LogicT.ifte
        (failure : LogicT (MStream Id Nat) Id Nat)
        (fun x => pure (x * 10))
        (pure 0)))
    [0]

  -- ifte single: applies th
  assertEq "ifte single"
    (allResults (LogicT.ifte
        (pure 5 : LogicT (MStream Id Nat) Id Nat)
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

  let grandparent (grandchild : String) : LogicT (List String) Id String := do
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
  let triples (n : Nat) : LogicT (List (Nat × Nat × Nat)) Id (Nat × Nat × Nat) := do
    let a ← LogicT.fromList (List.range n |>.map (· + 1))
    let b ← LogicT.fromList (List.range n |>.map (· + 1))
    let c ← LogicT.fromList (List.range n |>.map (· + 1))
    LogicT.guard (a * a + b * b == c * c)
    LogicT.guard (a ≤ b)  -- avoid duplicates
    pure (a, b, c)

  assertEq "pythagorean triples ≤ 15"
    (allResults (triples 15))
    [(3, 4, 5), (5, 12, 13), (6, 8, 10), (9, 12, 15)]

  -- Composite number check using once (lazy!)
  let divisors (n : Nat) : LogicT (MStream Id (Nat × Nat)) Id (Nat × Nat) := do
    let a ← LogicT.fromList (List.range (n - 2) |>.map (· + 2))
    let b ← LogicT.fromList (List.range (n - 2) |>.map (· + 2))
    LogicT.guard (a * b == n)
    pure (a, b)

  let isComposite (n : Nat) : Bool :=
    -- once only evaluates the first divisor pair (lazy!)
    match LogicT.msplit (LogicT.once (divisors n)) with
    | .nil => false
    | .cons _ _ => true

  assertEq "20 is composite" (isComposite 20) true
  assertEq "7 is not composite" (isComposite 7) false
  assertEq "12 is composite" (isComposite 12) true

  -- Prime check using lnot (lazy: only checks first alternative)
  let isPrime (n : Nat) : Bool :=
    n > 1 &&
      match LogicT.msplit (LogicT.lnot (divisors n) : LogicT (MStream Id Unit) Id Unit) with
      | .nil => false
      | .cons _ _ => true

  assertEq "7 is prime" (isPrime 7) true
  assertEq "20 is not prime" (isPrime 20) false
  assertEq "2 is prime" (isPrime 2) true
  assertEq "1 is not prime" (isPrime 1) false

-- ============================================================
-- MonadLift (transformer behavior)
-- ============================================================

def testMonadLift : IO Unit := do
  IO.println "MonadLift (transformer):"

  -- Lift IO into LogicT
  let l : LogicT (List Nat) IO Nat := do
    let x ← pure 1 <|> pure 2
    let y : Nat ← MonadLift.monadLift (pure 10 : IO Nat)
    pure (x + y)
  let result ← LogicT.observeAllT l
  assertEq "lift IO" result [11, 12]

  -- Multiple lifted effects
  let ref ← IO.mkRef (0 : Nat)
  let l2 : LogicT (List Nat) IO Nat := do
    let x ← pure 1 <|> pure 2 <|> pure 3
    MonadLift.monadLift (ref.modify (· + 1) : IO Unit)
    pure x
  let results ← LogicT.observeAllT l2
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
