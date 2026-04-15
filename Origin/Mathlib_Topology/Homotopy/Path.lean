/-
Extracted from Topology/Homotopy/Path.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homotopy between paths

In this file, we define a `Homotopy` between two `Path`s. In addition, we define a relation
`Homotopic` on `Path`s, and prove that it is an equivalence relation.

## Definitions

* `Path.Homotopy p₀ p₁` is the type of homotopies between paths `p₀` and `p₁`
* `Path.Homotopy.refl p` is the constant homotopy between `p` and itself
* `Path.Homotopy.symm F` is the `Path.Homotopy p₁ p₀` defined by reversing the homotopy
* `Path.Homotopy.trans F G`, where `F : Path.Homotopy p₀ p₁`, `G : Path.Homotopy p₁ p₂` is the
  `Path.Homotopy p₀ p₂` defined by putting the first homotopy on `[0, 1/2]` and the second on
  `[1/2, 1]`
* `Path.Homotopy.hcomp F G`, where `F : Path.Homotopy p₀ q₀` and `G : Path.Homotopy p₁ q₁` is
  a `Path.Homotopy (p₀.trans p₁) (q₀.trans q₁)`
* `Path.Homotopic p₀ p₁` is the relation saying that there is a homotopy between `p₀` and `p₁`
* `Path.Homotopic.setoid x₀ x₁` is the setoid on `Path`s from `Path.Homotopic`
* `Path.Homotopic.Quotient x₀ x₁` is the quotient type from `Path x₀ x₀` by `Path.Homotopic.setoid`

-/

universe u v

variable {X : Type u} {Y : Type v} [TopologicalSpace X] [TopologicalSpace Y]

variable {x₀ x₁ x₂ x₃ : X}

noncomputable section

open unitInterval

namespace Path

abbrev Homotopy (p₀ p₁ : Path x₀ x₁) :=
  ContinuousMap.HomotopyRel p₀.toContinuousMap p₁.toContinuousMap {0, 1}

namespace Homotopy

variable {p₀ p₁ : Path x₀ x₁}

theorem coeFn_injective : @Function.Injective (Homotopy p₀ p₁) (I × I → X) (⇑) :=
  DFunLike.coe_injective
