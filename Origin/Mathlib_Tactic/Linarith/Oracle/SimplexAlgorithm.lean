/-
Extracted from Tactic/Linarith/Oracle/SimplexAlgorithm.lean
Genuine: 4 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.Tactic.Linarith.Datatypes
import Mathlib.Tactic.Linarith.Oracle.SimplexAlgorithm.PositiveVector

/-!
# The oracle based on Simplex Algorithm

This file contains hooks to enable the use of the Simplex Algorithm in `linarith`.
The algorithm's entry point is the function `Linarith.SimplexAlgorithm.findPositiveVector`.
See the file `PositiveVector.lean` for details of how the procedure works.
-/

namespace Linarith.SimplexAlgorithm

open Mathlib

def preprocess (matType : ℕ → ℕ → Type) [UsableInSimplexAlgorithm matType] (hyps : List Comp)
    (maxVar : ℕ) : matType (maxVar + 1) (hyps.length) × List Nat :=
  let values : List (ℕ × ℕ × ℚ) := hyps.foldlIdx (init := []) fun idx cur comp =>
    cur ++ comp.coeffs.map fun (var, c) => (var, idx, c)

  let strictIndexes := hyps.findIdxs (·.str == Ineq.lt)
  (ofValues values, strictIndexes)

def postprocess (vec : Array ℚ) : Std.HashMap ℕ ℕ :=
  let common_den : ℕ := vec.foldl (fun acc item => acc.lcm item.den) 1
  let vecNat : Array ℕ := vec.map (fun x : ℚ => (x * common_den).floor.toNat)
  Std.HashMap.empty.insertMany <| vecNat.toList.enum.filter (fun ⟨_, item⟩ => item != 0)

end SimplexAlgorithm

open SimplexAlgorithm

def CertificateOracle.simplexAlgorithmSparse : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess SparseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

def CertificateOracle.simplexAlgorithmDense : CertificateOracle where
  produceCertificate hyps maxVar := do
    let (A, strictIndexes) := preprocess DenseMatrix hyps maxVar
    let vec ← findPositiveVector A strictIndexes
    return postprocess vec

end Linarith
