/-
Extracted from Probability/Kernel/Category/SFinKer.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# SFinKer

The category of measurable spaces with s-finite kernels is a copy-discard category.

## Main declarations

* `LargeCategory SFinKer`: the categorical structure on `SFinKer`.
* `MonoidalCategory SFinKer`: `SFinKer` is a monoidal category using the Cartesian product.
* `SymmetricCategory SFinKer`: `SFinKer` is a symmetric monoidal category.
* `CopyDiscardCategory SFinKer`: `SFinKer` is a copy-discard category.

## References
* [A synthetic approach to
Markov kernels, conditional independence and theorems on sufficient statistics][fritz2020]
-/

open CategoryTheory ProbabilityTheory MeasureTheory

universe u

structure SFinKer : Type (u + 1) where
  of ::
  /-- The underlying measurable space. -/
  carrier : Type u
  [str : MeasurableSpace carrier]

attribute [instance] SFinKer.str

-- INSTANCE (free from Core): :

namespace SFinKer
