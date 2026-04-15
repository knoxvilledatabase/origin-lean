/-
Extracted from Algebra/Category/Ring/Constructions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Constructions of (co)limits in `CommRingCat`

In this file we provide the explicit (co)cones for various (co)limits in `CommRingCat`, including
* tensor product is the pushout
* tensor product over `ℤ` is the binary coproduct
* `ℤ` is the initial object
* `0` is the strict terminal object
* Cartesian product is the product
* arbitrary direct product of a family of rings is the product object (Pi object)
* `RingHom.eqLocus` is the equalizer

-/

universe u u'

open CategoryTheory Limits TensorProduct

namespace CommRingCat

section Pushout

variable (R A B : Type u) [CommRing R] [CommRing A] [CommRing B]

variable [Algebra R A] [Algebra R B]

def pushoutCocone : Limits.PushoutCocone
    (CommRingCat.ofHom (algebraMap R A)) (CommRingCat.ofHom (algebraMap R B)) := by
  fapply Limits.PushoutCocone.mk
  · exact CommRingCat.of (A ⊗[R] B)
  · exact ofHom <| Algebra.TensorProduct.includeLeftRingHom (A := A)
  · exact ofHom <| Algebra.TensorProduct.includeRight.toRingHom (A := B)
  · ext r
    trans algebraMap R (A ⊗[R] B) r
    · exact Algebra.TensorProduct.includeLeft.commutes (R := R) r
    · exact (Algebra.TensorProduct.includeRight.commutes (R := R) r).symm
