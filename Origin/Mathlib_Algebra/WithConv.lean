/-
Extracted from Algebra/WithConv.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-! # Type synonym for linear map convolutive ring and intrinsic star

This files provides the type synonym `WithConv` which we will use in later files
to put the convolutive product on linear maps instance and the intrinsic star instance.
This is to ensure that we only have one multiplication, one unit, and one star.

This is given for any type `A` so that we can have `WithConv (A →ₗ[R] B)`,
`WithConv (A →L[R] B)`, `WithConv (Matrix m n R)`, etc.
-/

structure WithConv A where
  /-- Converts an element of `A` to `WithConv A`. -/ toConv ::
  /-- Converts an element of `WithConv A` back to `A`. -/ ofConv : A

namespace WithConv

open Lean.PrettyPrinter.Delaborator in
