/-
Extracted from Geometry/Manifold/VectorField/Pullback.lean
Genuine: 8 of 13 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!
# Vector fields in manifolds

We study functions of the form `V : Π (x : M) → TangentSpace I x` on a manifold, i.e.,
vector fields.

We define the pullback of a vector field under a map, as
`VectorField.mpullback I I' f V x := (mfderiv I I' f x).inverse (V (f x))`
(together with the same notion within a set). Note that the pullback uses the junk-value pattern:
if the derivative of the map is not invertible, then pullback is given the junk value zero.

See `Mathlib/Geometry/Manifold/VectorField/LieBracket.lean` for the Lie bracket of two vector
fields.

These definitions are given in the `VectorField` namespace because pullbacks, Lie brackets,
and so on, are notions that make sense in a variety of contexts.
We also prefix the notions with `m` to distinguish the manifold notions from the vector space
notions.

For notions that come naturally in other namespaces for dot notation, we specify `vectorField` in
the name to lift ambiguities. For instance, the fact that the Lie bracket of two smooth vector
fields is smooth is `ContMDiffAt.mlieBracket_vectorField`.

Note that a smoothness assumption for a vector field is written by seeing the vector field as
a function from `M` to its tangent bundle through a coercion, as in:
`MDifferentiableWithinAt I I.tangent (fun y ↦ (V y : TangentBundle I M)) s x`
(or `MDiffAt[s] (T% V) x`, for short).
-/

open Set Function Filter

open scoped Topology Manifold ContDiff

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {H : Type*} [TopologicalSpace H] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {H' : Type*} [TopologicalSpace H'] {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {I' : ModelWithCorners 𝕜 E' H'}
  {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M']
  {H'' : Type*} [TopologicalSpace H''] {E'' : Type*} [NormedAddCommGroup E''] [NormedSpace 𝕜 E'']
  {I'' : ModelWithCorners 𝕜 E'' H''}
  {M'' : Type*} [TopologicalSpace M''] [ChartedSpace H'' M'']
  {f : M → M'} {s t : Set M} {x x₀ : M}

-- INSTANCE (free from Core): {n

-- INSTANCE (free from Core): [IsManifold

-- INSTANCE (free from Core): [IsManifold

-- INSTANCE (free from Core): [IsManifold

namespace VectorField

section Pullback

/-! ### Pullback of vector fields in manifolds -/

open ContinuousLinearMap

variable {V W V₁ W₁ : Π (x : M'), TangentSpace I' x}

variable {c : 𝕜} {m n : WithTop ℕ∞} {t : Set M'} {y₀ : M'}

variable (I I') in

def mpullbackWithin (f : M → M') (V : Π (x : M'), TangentSpace I' x) (s : Set M) (x : M) :
    TangentSpace I x :=
  (mfderiv[s] f x).inverse (V (f x))

variable (I I') in

def mpullback (f : M → M') (V : Π (x : M'), TangentSpace I' x) (x : M) :
    TangentSpace I x :=
  (mfderiv% f x).inverse (V (f x))

lemma mpullbackWithin_const_smul_apply :
    mpullbackWithin I I' f (c • V) s x = c • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_smul_apply {g : M' → 𝕜} :
    mpullbackWithin I I' f (g • V) s x = g (f x) • mpullbackWithin I I' f V s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_const_smul :
    mpullbackWithin I I' f (c • V) s = c • mpullbackWithin I I' f V s := by
  ext x
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_smul {g : M' → 𝕜} :
    mpullbackWithin I I' f (g • V) s = (g ∘ f) • mpullbackWithin I I' f V s := by
  ext; simp [mpullbackWithin_apply]

lemma mpullbackWithin_add_apply :
    mpullbackWithin I I' f (V + V₁) s x =
      mpullbackWithin I I' f V s x + mpullbackWithin I I' f V₁ s x := by
  simp [mpullbackWithin_apply]

lemma mpullbackWithin_add :
    mpullbackWithin I I' f (V + V₁) s =
      mpullbackWithin I I' f V s + mpullbackWithin I I' f V₁ s := by
  ext x
  simp [mpullbackWithin_apply]
