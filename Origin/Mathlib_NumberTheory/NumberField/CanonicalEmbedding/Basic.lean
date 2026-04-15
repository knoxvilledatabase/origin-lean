/-
Extracted from NumberTheory/NumberField/CanonicalEmbedding/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Canonical embedding of a number field

The canonical embedding of a number field `K` of degree `n` is the ring homomorphism
`K →+* ℂ^n` that sends `x ∈ K` to `(φ_₁(x),...,φ_n(x))` where the `φ_i`'s are the complex
embeddings of `K`. Note that we do not choose an ordering of the embeddings, but instead map `K`
into the type `(K →+* ℂ) → ℂ` of `ℂ`-vectors indexed by the complex embeddings.

## Main definitions and results

* `NumberField.canonicalEmbedding`: the ring homomorphism `K →+* ((K →+* ℂ) → ℂ)` defined by
  sending `x : K` to the vector `(φ x)` indexed by `φ : K →+* ℂ`.

* `NumberField.canonicalEmbedding.integerLattice.inter_ball_finite`: the intersection of the
  image of the ring of integers by the canonical embedding and any ball centered at `0` of finite
  radius is finite.

* `NumberField.mixedEmbedding`: the ring homomorphism from `K` to the mixed space
  `K →+* ({ w // IsReal w } → ℝ) × ({ w // IsComplex w } → ℂ)` that sends `x ∈ K` to `(φ_w x)_w`
  where `φ_w` is the embedding associated to the infinite place `w`. In particular, if `w` is real
  then `φ_w : K →+* ℝ` and, if `w` is complex, `φ_w` is an arbitrary choice between the two complex
  embeddings defining the place `w`.

## Tags

number field, infinite places
-/

open Module

variable (K : Type*) [Field K]

namespace NumberField.canonicalEmbedding

def _root_.NumberField.canonicalEmbedding : K →+* ((K →+* ℂ) → ℂ) := Pi.ringHom fun φ => φ

theorem _root_.NumberField.canonicalEmbedding_injective [NumberField K] :
    Function.Injective (NumberField.canonicalEmbedding K) := RingHom.injective _

variable {K}
