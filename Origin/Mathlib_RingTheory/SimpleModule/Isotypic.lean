/-
Extracted from RingTheory/SimpleModule/Isotypic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Isotypic modules and isotypic components

## Main definitions

* `IsIsotypicOfType R M S` means that all simple submodules of the `R`-module `M`
  are isomorphic to `S`. Such a module `M` is isomorphic to a finsupp over `S`,
  see `IsIsotypicOfType.linearEquiv_finsupp`.

* `IsIsotypic R M` means that all simple submodules of the `R`-module `M`
  are isomorphic to each other.

* `isotypicComponent R M S` is the sum of all submodules of `M` isomorphic to `S`.

* `isotypicComponents R M` is the set of all nontrivial isotypic components of `M`
  (where `S` is taken to be simple submodules).

* `Submodule.IsFullyInvariant N` means that the submodule `N` of an `R`-module `M` is mapped into
  itself by all endomorphisms of `M`. The `fullyInvariantSubmodule`s of `M` form a complete
  lattice, which is atomic if `M` is semisimple, in which case the atoms are the isotypic
  components of `M`. A fully invariant submodule of a semiring as a module over itself
  is simply a two-sided ideal, see `isFullyInvariant_iff_isTwoSided`.

* `iSupIndep.ringEquiv`, `iSupIndep.algEquiv`: if `M` is the direct sum of fully invariant
  submodules `Nᵢ`, then `End R M` is isomorphic to `Πᵢ End R Nᵢ`. This can be applied to
  the isotypic components of a semisimple module `M`, yielding `IsSemisimpleModule.endAlgEquiv`.

## Keywords

isotypic component, fully invariant submodule

-/

universe u

variable (R₀ R : Type*) (M : Type u) (N S : Type*) [CommSemiring R₀]
  [Ring R] [Algebra R₀ R] [AddCommGroup M] [AddCommGroup N]
  [AddCommGroup S] [Module R M] [Module R N] [Module R S]

def IsIsotypicOfType : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], Nonempty (m ≃ₗ[R] S)

def IsIsotypic : Prop := ∀ (m : Submodule R M) [IsSimpleModule R m], IsIsotypicOfType R M m

variable {R M S} in

theorem IsIsotypicOfType.isIsotypic (h : IsIsotypicOfType R M S) : IsIsotypic R M :=
  fun m _ m' _ ↦ ⟨(h m').some.trans (h m).some.symm⟩
