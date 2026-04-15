/-
Extracted from LinearAlgebra/Span/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The span of a set of vectors, as a submodule

* `Submodule.span s` is defined to be the smallest submodule containing the set `s`.

## Notation

* We introduce the notation `R ∙ v` for the span of a singleton, `Submodule.span R {v}`.  This is
  `\span`, not the same as the scalar multiplication `•`/`\bub`.

-/

assert_not_exists Field

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {x : M} (p p' : Submodule R M)

variable [Semiring R₂] {σ₁₂ : R →+* R₂}

variable [AddCommMonoid M₂] [Module R₂ M₂]

variable {F : Type*} [FunLike F M M₂] [SemilinearMapClass F σ₁₂ M M₂]

variable (R) in

def span (s : Set M) : Submodule R M :=
  sInf { p | s ⊆ p }
