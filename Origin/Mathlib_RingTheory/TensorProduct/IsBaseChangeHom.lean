/-
Extracted from RingTheory/TensorProduct/IsBaseChangeHom.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! # Base change properties for modules of linear maps

* `IsBaseChange.linearMapRight`:
  If `M` is finite free and `P` is a base change of `N` to `S`,
  then `M →ₗ[R] P` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.linearMapLeftRight`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  if `Q` is a base change of `N` to `S`,
  then `P →ₗ[S] Q` is a base change of `M →ₗ[R] N` to `S`.

* `IsBaseChange.end`:
  If `M` is finite free and `P` is a base change of `M` to `S`,
  then `P →ₗ[S] P` is a base change of `M →ₗ[R] M` to `S`.

-/

namespace IsBaseChange

open LinearMap TensorProduct Module

variable {R : Type*} [CommSemiring R]
    (S : Type*) [CommSemiring S] [Algebra R S]
    (M : Type*) [AddCommMonoid M] [Module R M]
    {N : Type*} [AddCommMonoid N] [Module R N]
    {P : Type*} [AddCommMonoid P] [Module R P]

section LinearMapRight

variable [Module S P] [IsScalarTower R S P]

def linearMapRightBaseChangeHom (ε : N →ₗ[R] P) :
    (S ⊗[R] (M →ₗ[R] N)) →ₗ[S] (M →ₗ[R] P) where
  toAddHom := (TensorProduct.lift {
    toFun s := s • (LinearMap.compRight R ε (M := M))
    map_add' x y := by ext; simp [add_smul]
    map_smul' r s := by simp }).toAddHom
  map_smul' s x := by
    simp only [AddHom.toFun_eq_coe, coe_toAddHom, RingHom.id_apply]
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp [smul_add, hx, hy]
    | tmul t f => simp [TensorProduct.smul_tmul', mul_smul]

variable [Free R M] [Module.Finite R M]

variable {S}

noncomputable def linearMapRightBaseChangeEquiv
    {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] (M →ₗ[R] P) := by
  apply LinearEquiv.ofBijective (linearMapRightBaseChangeHom S M ε)
  let b := Free.chooseBasis R M
  set ι := Free.ChooseBasisIndex R M
  have := Free.ChooseBasisIndex.fintype R M
  let e := (b.repr.congrLeft N R).trans (Finsupp.llift N R R ι).symm
  let f := (b.repr.congrLeft P S).trans (Finsupp.llift P R S ι).symm
  let h := linearMapRightBaseChangeHom S M ε
  let e' : S ⊗[R] (M →ₗ[R] N) ≃ₗ[S] S ⊗[R] (ι → N) :=
    LinearEquiv.baseChange R S (M →ₗ[R] N) (ι → N) e
  let h' := (f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε)).comp e'.symm.toLinearMap
  suffices Function.Bijective h' by simpa [h'] using this
  suffices h' = (finitePow ι ibc).equiv by
    simp only [this]
    apply LinearEquiv.bijective
  suffices f.toLinearMap.comp (linearMapRightBaseChangeHom S M ε) =
      (finitePow ι ibc).equiv.toLinearMap.comp e'.toLinearMap by
    simp [h', this, ← LinearEquiv.trans_assoc e'.symm e']
  ext φ i
  simp
  simp [f, e', linearMapRightBaseChangeHom, LinearEquiv.baseChange, equiv_tmul,
    LinearEquiv.congrLeft, e]

theorem linearMapRight {ε : N →ₗ[R] P} (ibc : IsBaseChange S ε) :
    IsBaseChange S (LinearMap.compRight (M := M) R ε) := by
  apply of_equiv (linearMapRightBaseChangeEquiv M ibc)
  intro f
  simp [linearMapRightBaseChangeEquiv, linearMapRightBaseChangeHom]

end LinearMapRight

section LinearMapLeftRight

variable {S M}
  {Q : Type*} [AddCommMonoid Q] [Module R Q]
  [Module S P] [IsScalarTower R S P]
  [Module S Q] [IsScalarTower R S Q]

noncomputable def linearMapLeftRightHom {α : M →ₗ[R] P} (j : IsBaseChange S α)
    (β : N →ₗ[R] Q) :
    (M →ₗ[R] N) →ₗ[R] (P →ₗ[S] Q) :=
  ((LinearMap.llcomp (σ₂₃ := RingHom.id S) S P (S ⊗[R] M) Q).flip
    j.equiv.symm.toLinearMap) ∘ₗ
    (liftBaseChangeEquiv S).toLinearMap.restrictScalars R ∘ₗ
      (compRight R β (M := M))
