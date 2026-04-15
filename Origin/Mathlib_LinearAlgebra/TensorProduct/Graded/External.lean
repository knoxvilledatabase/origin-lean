/-
Extracted from LinearAlgebra/TensorProduct/Graded/External.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Graded tensor products over graded algebras

The graded tensor product $A \hat\otimes_R B$ is imbued with a multiplication defined on homogeneous
tensors by:

$$(a \otimes b) \cdot (a' \otimes b') = (-1)^{\deg a' \deg b} (a \cdot a') \otimes (b \cdot b')$$

where $A$ and $B$ are algebras graded by `ℕ`, `ℤ`, or `ZMod 2` (or more generally, any index
that satisfies `Module ι (Additive ℤˣ)`).

The results for internally-graded algebras (via `GradedAlgebra`) are elsewhere, as is the type
`GradedTensorProduct`.

## Main results

* `TensorProduct.gradedComm`: the symmetric braiding operator on the tensor product of
  externally-graded rings.
* `TensorProduct.gradedMul`: the previously-described multiplication on externally-graded rings, as
  a bilinear map.

## Implementation notes

Rather than implementing the multiplication directly as above, we first implement the canonical
non-trivial braiding sending $a \otimes b$ to $(-1)^{\deg a' \deg b} (b \otimes a)$, as the
multiplication follows trivially from this after some point-free nonsense.

## References

* https://math.stackexchange.com/q/202718/1896
* [*Algebra I*, Bourbaki : Chapter III, §4.7, example (2)][bourbaki1989]

-/

open scoped TensorProduct DirectSum

variable {R ι : Type*}

namespace TensorProduct

variable [CommSemiring ι] [Module ι (Additive ℤˣ)] [DecidableEq ι]

variable (𝒜 : ι → Type*) (ℬ : ι → Type*)

variable [CommRing R]

variable [∀ i, AddCommGroup (𝒜 i)] [∀ i, AddCommGroup (ℬ i)]

variable [∀ i, Module R (𝒜 i)] [∀ i, Module R (ℬ i)]

-- INSTANCE (free from Core): (i

open DirectSum (lof)

variable (R)

section gradedComm

local notation "𝒜ℬ" => (fun i : ι × ι => 𝒜 (Prod.fst i) ⊗[R] ℬ (Prod.snd i))

local notation "ℬ𝒜" => (fun i : ι × ι => ℬ (Prod.fst i) ⊗[R] 𝒜 (Prod.snd i))

def gradedCommAux : DirectSum _ 𝒜ℬ →ₗ[R] DirectSum _ ℬ𝒜 :=
  DirectSum.toModule R _ _ fun i =>
    have o := DirectSum.lof R _ ℬ𝒜 (i.2, i.1)
    have s : ℤˣ := ((-1 : ℤˣ) ^ (i.1 * i.2 : ι) : ℤˣ)
    (s • o) ∘ₗ (TensorProduct.comm R _ _).toLinearMap
