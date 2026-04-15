/-
Extracted from Algebra/Module/CharacterModule.lean
Genuine: 1 of 4 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Character module of a module

For commutative ring `R` and an `R`-module `M` and an injective module `D`, its character module
`M⋆` is defined to be `R`-linear maps `M ⟶ D`.

`M⋆` also has an `R`-module structure given by `(r • f) m = f (r • m)`.

## Main results

- `CharacterModuleFunctor` : the contravariant functor of `R`-modules where `M ↦ M⋆` and
  an `R`-linear map `l : M ⟶ N` induces an `R`-linear map `l⋆ : f ↦ f ∘ l` where `f : N⋆`.
- `LinearMap.dual_surjective_of_injective` : If `l` is injective then `l⋆` is surjective,
  in another word taking character module as a functor sends monos to epis.
- `CharacterModule.homEquiv` : there is a bijection between linear map `Hom(N, M⋆)` and
  `(N ⊗ M)⋆` given by `curry` and `uncurry`.

-/

open CategoryTheory

universe uR uA uB

variable (R : Type uR) [CommRing R]

variable (A : Type uA) [AddCommGroup A]

variable (A' : Type*) [AddCommGroup A']

variable (B : Type uB) [AddCommGroup B]

def CharacterModule : Type uA := A →+ AddCircle (1 : ℚ)

namespace CharacterModule

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :
