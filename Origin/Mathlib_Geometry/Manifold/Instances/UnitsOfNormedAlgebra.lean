/-
Extracted from Geometry/Manifold/Instances/UnitsOfNormedAlgebra.lean
Genuine: 1 of 6 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Units of a normed algebra

We construct the Lie group structure on the group of units of a complete normed `𝕜`-algebra `R`. The
group of units `Rˣ` has a natural `C^n` manifold structure modelled on `R` given by its embedding
into `R`. Together with the smoothness of the multiplication and inverse of its elements, `Rˣ` forms
a Lie group.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`ContinuousLinearMap.toNormedAlgebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`), as demonstrated by:
```
example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : WithTop ℕ∞) :
    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance
```
-/

noncomputable section

open scoped Manifold ContDiff

namespace Units

variable {R : Type*} [NormedRing R] [CompleteSpace R] {n : WithTop ℕ∞}

-- INSTANCE (free from Core): :

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [NormedAlgebra 𝕜 R]

-- INSTANCE (free from Core): :

lemma contMDiff_val : ContMDiff 𝓘(𝕜, R) 𝓘(𝕜, R) n (val : Rˣ → R) :=
  contMDiff_isOpenEmbedding Units.isOpenEmbedding_val

-- INSTANCE (free from Core): :

example {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V] [CompleteSpace V] (n : WithTop ℕ∞) :

    LieGroup 𝓘(𝕜, V →L[𝕜] V) n (V →L[𝕜] V)ˣ := inferInstance

end Units
