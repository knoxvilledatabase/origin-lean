/-
Extracted from CategoryTheory/Monoidal/Functor/Types.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Convert from `Applicative` to `CategoryTheory.Functor.LaxMonoidal`

This allows us to use Lean's `Type`-based applicative functors in category theory.

-/

namespace CategoryTheory

variable (F : Type* → Type*) [Applicative F] [LawfulApplicative F]

attribute [local simp] map_seq seq_map_assoc types_tensorObj_def types_tensorUnit_def
  LawfulApplicative.pure_seq LawfulApplicative.seq_assoc in
