/-
Extracted from Algebra/Category/ModuleCat/Topology/Homology.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!

# `TopModuleCat` is a `CategoryWithHomology`

`TopModuleCat R`, the category of topological `R`-modules, is not an abelian category.
But since the topology on subquotients is well-defined, we can still talk about homology in this
category. See the `CategoryWithHomology (TopModuleCat R)` instance in this file.

-/

universe v u

open CategoryTheory Limits

namespace TopModuleCat

variable {R : Type u} [Ring R] [TopologicalSpace R]

variable {M N : TopModuleCat.{v} R} (φ : M ⟶ N)

section kernel

abbrev ker : TopModuleCat R := .of R φ.hom.ker

def kerι : ker φ ⟶ M := ofHom ⟨Submodule.subtype _, continuous_subtype_val⟩

-- INSTANCE (free from Core): :
