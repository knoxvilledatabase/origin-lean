/-
Extracted from Algebra/Module/Presentation/Cokernel.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Presentation of a cokernel

If `f : M₁ →ₗ[A] M₂` is a linear map between modules,
`pres₂` is a presentation of `M₂` and `g₁ : ι → M₁` is
a family of generators of `M₁` (which is expressed as
`hg₁ : Submodule.span A (Set.range g₁) = ⊤`), then we
provide a way to obtain a presentation of the cokernel of `f`.
It requires an additional data `data : pres₂.CokernelData f g₁`,
which consists of liftings of the images by `f` of
the generators of `M₁` as linear combinations of the
generators of `M₂`. Then, we obtain a presentation
`pres₂.cokernel data hg₁ : Presentation A (M₂ ⧸ LinearMap.range f)`.

More generally, if we have an exact sequence `M₁ → M₂ → M₃ → 0`,
we obtain a presentation of `M₃`, see `Presentation.ofExact`.

-/

universe w w₁ w₂₀ w₂₁ v₁ v₂ v₃ u

namespace Module

variable {A : Type u} [Ring A] {M₁ : Type v₁} {M₂ : Type v₂} {M₃ : Type v₃}
  [AddCommGroup M₁] [Module A M₁] [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₃] [Module A M₃]

namespace Presentation

section Cokernel

variable (pres₂ : Presentation.{w₂₀, w₂₁} A M₂) (f : M₁ →ₗ[A] M₂)
  {ι : Type w₁} (g₁ : ι → M₁)

structure CokernelData where
  /-- a lifting of `f (g₁ i)` in `pres₂.G →₀ A` -/
  lift (i : ι) : pres₂.G →₀ A
  π_lift (i : ι) : pres₂.π (lift i) = f (g₁ i)
