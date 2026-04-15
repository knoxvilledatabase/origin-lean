/-
Extracted from RingTheory/TensorProduct/Nontrivial.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Nontriviality of tensor product of algebras

This file contains some more results on nontriviality of tensor product of algebras.

-/

open TensorProduct

namespace Algebra.TensorProduct

theorem nontrivial_of_algebraMap_injective_of_isDomain
    (R A B : Type*) [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (ha : Function.Injective (algebraMap R A)) (hb : Function.Injective (algebraMap R B))
    [IsDomain A] [IsDomain B] : Nontrivial (A ⊗[R] B) := by
  haveI := ha.isDomain _
  let FR := FractionRing R
  let FA := FractionRing A
  let FB := FractionRing B
  let fa : FR →ₐ[R] FA := IsFractionRing.liftAlgHom (g := Algebra.ofId R FA)
    ((IsFractionRing.injective A FA).comp ha)
  let fb : FR →ₐ[R] FB := IsFractionRing.liftAlgHom (g := Algebra.ofId R FB)
    ((IsFractionRing.injective B FB).comp hb)
  algebraize_only [fa.toRingHom, fb.toRingHom]
  letI : CompatibleSMul FR R FA FB := CompatibleSMul.isScalarTower
  exact Algebra.TensorProduct.mapOfCompatibleSMul FR R R FA FB |>.comp
    (Algebra.TensorProduct.map (IsScalarTower.toAlgHom R A FA) (IsScalarTower.toAlgHom R B FB))
    |>.toRingHom.domain_nontrivial

end Algebra.TensorProduct
