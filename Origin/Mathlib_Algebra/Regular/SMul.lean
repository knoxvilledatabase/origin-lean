/-
Extracted from Algebra/Regular/SMul.lean
Genuine: 2 of 6 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Action of regular elements on a module

We introduce `M`-regular elements, in the context of an `R`-module `M`.  The corresponding
predicate is called `IsSMulRegular`.

There are very limited typeclass assumptions on `R` and `M`, but the "mathematical" case of interest
is a commutative ring `R` acting on a module `M`. Since the properties are "multiplicative", there
is no actual requirement of having an addition, but there is a zero in both `R` and `M`.
Scalar multiplications involving `0` are, of course, all trivial.

The defining property is that an element `a ∈ R` is `M`-regular if the scalar multiplication map
`M → M`, defined by `m ↦ a • m`, is injective.

This property is the direct generalization to modules of the property `IsLeftRegular` defined in
`Algebra/Regular`.  Lemma `isLeftRegular_iff` shows that indeed the two notions
coincide.
-/

variable {R S : Type*} (M : Type*) {a b : R} {s : S}

def IsSMulRegular [SMul R M] (c : R) :=
  Function.Injective ((c • ·) : M → M)

variable {M}

lemma isSMulRegular_map [SMul R M] [SMul S M] (f : R → S) (smul : ∀ m : M, f a • m = a • m) :
    IsSMulRegular M (f a) ↔ IsSMulRegular M a := by simp [IsSMulRegular, smul]

protected alias ⟨IsSMulRegular.of_map, IsSMulRegular.map⟩ := isSMulRegular_map

namespace IsSMulRegular
