/-
Extracted from Analysis/Normed/Affine/ContinuousAffineMap.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Norm on the continuous affine maps between normed vector spaces.

We define a norm on the space of continuous affine maps between normed vector spaces by defining the
norm of `f : V →ᴬ[𝕜] W` to be `‖f‖ = max ‖f 0‖ ‖f.cont_linear‖`. This is chosen so that we have a
linear isometry: `(V →ᴬ[𝕜] W) ≃ₗᵢ[𝕜] W × (V →L[𝕜] W)`.

The abstract picture is that for an affine space `P` modelled on a vector space `V`, together with
a vector space `W`, there is an exact sequence of `𝕜`-modules: `0 → C → A → L → 0` where `C`, `A`
are the spaces of constant and affine maps `P → W` and `L` is the space of linear maps `V → W`.

Any choice of a base point in `P` corresponds to a splitting of this sequence so in particular if we
take `P = V`, using `0 : V` as the base point provides a splitting, and we prove this is an
isometric decomposition.

On the other hand, choosing a base point breaks the affine invariance so the norm fails to be
submultiplicative: for a composition of maps, we have only `‖f.comp g‖ ≤ ‖f‖ * ‖g‖ + ‖f 0‖`.

## Main definitions:

* `ContinuousAffineMap.hasNorm`
* `ContinuousAffineMap.norm_comp_le`
* `ContinuousAffineMap.toConstProdContinuousLinearMap`

-/

namespace ContinuousAffineMap

variable {𝕜 R V W W₂ : Type*}

variable [NormedAddCommGroup V] [NormedAddCommGroup W] [NormedAddCommGroup W₂]

variable [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 V] [NormedSpace 𝕜 W] [NormedSpace 𝕜 W₂]

section NormedSpaceStructure

variable (f : V →ᴬ[𝕜] W)

-- INSTANCE (free from Core): hasNorm

theorem norm_contLinear_le : ‖f.contLinear‖ ≤ ‖f‖ :=
  le_max_right _ _

theorem norm_image_zero_le : ‖f 0‖ ≤ ‖f‖ :=
  le_max_left _ _
