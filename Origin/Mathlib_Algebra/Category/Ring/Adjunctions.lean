/-
Extracted from Algebra/Category/Ring/Adjunctions.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Adjunctions in `CommRingCat`

## Main results
- `CommRingCat.adj`: `σ ↦ ℤ[σ]` is left adjoint to the forgetful functor `CommRingCat ⥤ Type`.
- `CommRingCat.coyonedaAdj`: `Fun(-, R)` is left adjoint to `Hom_{CRing}(R, -)`.
- `CommRingCat.monoidAlgebraAdj`: `G ↦ R[G]` as `CommGrpCat ⥤ R-Alg` is left adjoint to `S ↦ Sˣ`.
- `CommRingCat.unitsAdj`: `G ↦ ℤ[G]` is left adjoint to `S ↦ Sˣ`.

-/

noncomputable section

universe v u

open MvPolynomial Opposite

open CategoryTheory

namespace CommRingCat

def free : Type u ⥤ CommRingCat.{u} where
  obj α := of (MvPolynomial α ℤ)
  map {X Y} f := ofHom (↑(rename f : _ →ₐ[ℤ] _) : MvPolynomial X ℤ →+* MvPolynomial Y ℤ)
