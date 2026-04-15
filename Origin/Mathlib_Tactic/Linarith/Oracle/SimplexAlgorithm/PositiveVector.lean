/-
Extracted from Tactic/Linarith/Oracle/SimplexAlgorithm/PositiveVector.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Lean.Meta.Basic
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.SimplexAlgorithm
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.Gauss

/-!
# `linarith` certificate search as an LP problem

`linarith` certificate search can easily be reduced to the following problem:
given the matrix `A` and the list `strictIndexes`,
find the nonnegative vector `v` such that some of its coordinates from
the `strictIndexes` are positive and `A v = 0`.

The function `findPositiveVector` solves this problem.

# Algorithm sketch

1. We translate the problem stated above to some Linear Programming problem. See `stateLP` for
  details. Let us denote the corresponding matrix `B`.

2. We solve the equation `B x = 0` using Gauss Elimination, splitting the set of variables into
  *free* variables, which can take any value,
  and *basic* variables which are linearly expressed through the free one.
  This gives us an initial tableau for the Simplex Algorithm.
  See `Linarith.SimplexAlgorithm.Gauss.getTableau`.

3. We run the Simplex Algorithm until it finds a solution.
  See the file `SimplexAlgorithm.lean`.

-/

namespace Linarith.SimplexAlgorithm

variable {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]

def stateLP {n m : Nat} (A : matType n m) (strictIndexes : List Nat) : matType (n + 2) (m + 3) :=
  /- +2 due to shifting by `f` and `z` -/
  let objectiveRow : List (Nat × Nat × Rat) :=
    (0, 0, -1) :: strictIndexes.map fun idx => (0, idx + 2, 1)
  let constraintRow : List (Nat × Nat × Rat) :=
    [(1, 1, 1), (1, m + 2, -1)] ++ (List.range m).map (fun i => (1, i + 2, 1))

  let valuesA := getValues A |>.map fun (i, j, v) => (i + 2, j + 2, v)

  ofValues (objectiveRow ++ constraintRow ++ valuesA)

def extractSolution (tableau : Tableau matType) : Array Rat := Id.run do
  let mut ans : Array Rat := Array.mkArray (tableau.basic.size + tableau.free.size - 3) 0
  for i in [1:tableau.basic.size] do
    ans := ans.set! (tableau.basic[i]! - 2) <| tableau.mat[(i, tableau.free.size - 1)]!
  return ans

def findPositiveVector {n m : Nat} {matType : Nat → Nat → Type} [UsableInSimplexAlgorithm matType]
    (A : matType n m) (strictIndexes : List Nat) : Lean.Meta.MetaM <| Array Rat := do
  /- State the linear programming problem. -/
  let B := stateLP A strictIndexes

  /- Using Gaussian elimination split variable into free and basic forming the tableau that will be
  operated by the Simplex Algorithm. -/
  let initTableau ← Gauss.getTableau B

  /- Run the Simplex Algorithm and extract the solution. -/
  let res ← runSimplexAlgorithm.run initTableau
  if res.fst.isOk then
    return extractSolution res.snd
  else
    throwError "Simplex Algorithm failed"

end SimplexAlgorithm

end Linarith
