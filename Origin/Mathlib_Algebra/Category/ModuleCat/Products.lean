/-
Extracted from Algebra/Category/ModuleCat/Products.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The concrete products in the category of modules are products in the categorical sense.
-/

open CategoryTheory

open CategoryTheory.Limits

universe u v w

namespace ModuleCat

variable {R : Type u} [Ring R]

variable {ι : Type v} (Z : ι → ModuleCat.{max v w} R)

section product

def productCone : Fan Z :=
  Fan.mk (ModuleCat.of R (∀ i : ι, Z i)) fun i =>
    ofHom (LinearMap.proj i : (∀ i : ι, Z i) →ₗ[R] Z i)

def productConeIsLimit : IsLimit (productCone Z) where
  lift s := ofHom (LinearMap.pi fun j => (s.π.app ⟨j⟩).hom : s.pt →ₗ[R] ∀ i : ι, Z i)
  uniq s m w := by
    ext x
    funext i
    exact DFunLike.congr_fun (congr_arg Hom.hom (w ⟨i⟩)) x

variable [HasProduct Z]

noncomputable def piIsoPi : ∏ᶜ Z ≅ ModuleCat.of R (∀ i, Z i) :=
  limit.isoLimitCone ⟨_, productConeIsLimit Z⟩
