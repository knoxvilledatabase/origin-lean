/-
Extracted from LinearAlgebra/Span/Basic.lean
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

variable {R R₂ K M M₂ V S : Type*}

namespace Submodule

open Function Set

open Pointwise

section AddCommMonoid

variable [Semiring R] [AddCommMonoid M] [Module R M]

variable {x : M} (p p' : Submodule R M)

variable [Semiring R₂] {σ₁₂ : R →+* R₂}

variable [AddCommMonoid M₂] [Module R₂ M₂]

variable {s t : Set M}

lemma _root_.AddSubmonoid.toNatSubmodule_closure (s : Set M) :
    (AddSubmonoid.closure s).toNatSubmodule = .span ℕ s :=
  (Submodule.span_le.mpr AddSubmonoid.subset_closure).antisymm'
    ((Submodule.span ℕ s).toAddSubmonoid.closure_le.mpr Submodule.subset_span)
