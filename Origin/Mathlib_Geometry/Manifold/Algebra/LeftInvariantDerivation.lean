/-
Extracted from Geometry/Manifold/Algebra/LeftInvariantDerivation.lean
Genuine: 3 of 7 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!

# Left invariant derivations

In this file we define the concept of left invariant derivations for a Lie group. The concept is
analogous to the more classical concept of left invariant vector fields, and it holds that the
derivation associated to a vector field is left invariant iff the field is.

Moreover we prove that `LeftInvariantDerivation I G` has the structure of a Lie algebra, hence
implementing one of the possible definitions of the Lie algebra attached to a Lie group.

Note that one can also define a Lie algebra on the space of left-invariant vector fields
(see `instLieAlgebraGroupLieAlgebra`). For finite-dimensional `C^∞` real manifolds, the space of
derivations can be canonically identified with the tangent space, and we recover the same Lie
algebra structure (TODO: prove this). In other smoothness classes or on other
fields, this identification is not always true, though, so the derivations point of view does not
work in these settings. The left-invariant vector fields should
therefore be favored to construct a theory of Lie groups in suitable generality.
-/

noncomputable section

open scoped LieGroup Manifold Derivation ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞} {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H) (G : Type*)
  [TopologicalSpace G] [ChartedSpace H G] [Monoid G] [ContMDiffMul I ∞ G] (g h : G)

structure LeftInvariantDerivation extends Derivation 𝕜 C^∞⟮I, G; 𝕜⟯ C^∞⟮I, G; 𝕜⟯ where
  left_invariant'' :
    ∀ g, 𝒅ₕ (smoothLeftMul_one I g) (Derivation.evalAt 1 toDerivation) =
      Derivation.evalAt g toDerivation

variable {I G}

namespace LeftInvariantDerivation

-- INSTANCE (free from Core): :

attribute [coe] toDerivation

theorem toDerivation_injective :
    Function.Injective (toDerivation : LeftInvariantDerivation I G → _) :=
  fun X Y h => by cases X; cases Y; congr

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {r : 𝕜} {X Y : LeftInvariantDerivation I G} {f f' : C^∞⟮I, G; 𝕜⟯}

theorem coe_injective :
    @Function.Injective (LeftInvariantDerivation I G) (_ → C^∞⟮I, G; 𝕜⟯) DFunLike.coe :=
  DFunLike.coe_injective
