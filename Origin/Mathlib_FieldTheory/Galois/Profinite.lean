/-
Extracted from FieldTheory/Galois/Profinite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Galois Group as a profinite group

In this file, we prove that given a field extension `K/k`, there is a continuous isomorphism between
`Gal(K/k)` and the limit of `Gal(L/k)`, where `L` is a finite Galois intermediate field ordered by
inverse inclusion, thus making `Gal(K/k)` profinite as a limit of finite groups.

## Main definitions and results

In a field extension `K/k`

* `finGaloisGroup L` : The (finite) Galois group `Gal(L/k)` associated to a
  `L : FiniteGaloisIntermediateField k K` `L`.

* `finGaloisGroupMap` : For `FiniteGaloisIntermediateField` s `L₁` and `L₂` with `L₂ ≤ L₁`
  giving the restriction of `Gal(L₁/k)` to `Gal(L₂/k)`

* `finGaloisGroupFunctor` : The functor from `FiniteGaloisIntermediateField`
  (ordered by reverse inclusion) to `FiniteGrp`, mapping each `FiniteGaloisIntermediateField L`
  to `Gal (L/k)`.

* `InfiniteGalois.algEquivToLimit` : The homomorphism from `Gal(K/k)` to
  `limit (asProfiniteGaloisGroupFunctor k K)`, induced by the projections from `Gal(K/k)` to
  any `Gal(L/k)` where `L` is a `FiniteGaloisIntermediateField`.

* `InfiniteGalois.limitToAlgEquiv` : The inverse of `InfiniteGalois.algEquivToLimit`, in which
  the elements of `Gal(K/k)` are constructed pointwise.

* `InfiniteGalois.mulEquivToLimit` : The mulEquiv obtained from combining the above two.

* `InfiniteGalois.mulEquivToLimit_continuous` : The inverse of `InfiniteGalois.mulEquivToLimit`
  is continuous.

* `InfiniteGalois.continuousMulEquivToLimit` ：The `ContinuousMulEquiv` between `Gal(K/k)` and
  `limit (asProfiniteGaloisGroupFunctor k K)` given by `InfiniteGalois.mulEquivToLimit`

* `InfiniteGalois.ProfiniteGalGrp` : `Gal(K/k)` as a profinite group as there is
  a `ContinuousMulEquiv` to a `ProfiniteGrp` given above.

* `InfiniteGalois.restrictNormalHomContinuous` : Any `restrictNormalHom` is continuous.

-/

open CategoryTheory Opposite

variable {k K : Type*} [Field k] [Field K] [Algebra k K]

section Profinite

def FiniteGaloisIntermediateField.finGaloisGroup (L : FiniteGaloisIntermediateField k K) :
    FiniteGrp :=
  letI := AlgEquiv.fintype k L
  FiniteGrp.of Gal(L/k)

noncomputable def finGaloisGroupMap {L₁ L₂ : (FiniteGaloisIntermediateField k K)ᵒᵖ}
    (le : L₁ ⟶ L₂) : L₁.unop.finGaloisGroup ⟶ L₂.unop.finGaloisGroup :=
  haveI : Normal k L₂.unop := IsGalois.to_normal
  letI : Algebra L₂.unop L₁.unop := RingHom.toAlgebra (Subsemiring.inclusion <| leOfHom le.1)
  haveI : IsScalarTower k L₂.unop L₁.unop := IsScalarTower.of_algebraMap_eq (congrFun rfl)
  FiniteGrp.ofHom (AlgEquiv.restrictNormalHom L₂.unop)

namespace finGaloisGroupMap
