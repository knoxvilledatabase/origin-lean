/-
Extracted from RingTheory/Coalgebra/TensorProduct.lean
Genuine: 6 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.Algebra.Category.CoalgebraCat.ComonEquivalence

noncomputable section

/-!
# Tensor products of coalgebras

Given two `R`-coalgebras `M, N`, we can define a natural comultiplication map
`Δ : M ⊗[R] N → (M ⊗[R] N) ⊗[R] (M ⊗[R] N)` and counit map `ε : M ⊗[R] N → R` induced by
the comultiplication and counit maps of `M` and `N`. These `Δ, ε` are declared as linear maps
in `TensorProduct.instCoalgebraStruct` in `Mathlib.RingTheory.Coalgebra.Basic`.

In this file we show that `Δ, ε` satisfy the axioms of a coalgebra, and also define other data
in the monoidal structure on `R`-coalgebras, like the tensor product of two coalgebra morphisms
as a coalgebra morphism.

## Implementation notes

We keep the linear maps underlying `Δ, ε` and other definitions in this file syntactically equal
to the corresponding definitions for tensor products of modules in the hope that this makes
life easier. However, to fill in prop fields, we use the API in
`Mathlib.Algebra.Category.CoalgebraCat.ComonEquivalence`. That file defines the monoidal category
structure on coalgebras induced by an equivalence with comonoid objects in the category of modules,
`CoalgebraCat.instMonoidalCategoryAux`, but we do not declare this as an instance - we just use it
to prove things. Then, we use the definitions in this file to make a monoidal category instance on
`CoalgebraCat R` in `Mathlib.Algebra.Category.CoalgebraCat.Monoidal` that has simpler data.

However, this approach forces our coalgebras to be in the same universe as the base ring `R`,
since it relies on the monoidal category structure on `ModuleCat R`, which is currently
universe monomorphic. Any contribution that achieves universe polymorphism would be welcome. For
instance, the tensor product of coalgebras in the
[FLT repo](https://github.com/ImperialCollegeLondon/FLT/blob/eef74b4538c8852363936dfaad23e6ffba72eca5/FLT/mathlibExperiments/Coalgebra/TensorProduct.lean)
is already universe polymorphic since it does not go via category theory.

-/

universe v u

open CategoryTheory

open scoped TensorProduct

section

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N] [Coalgebra R M] [Coalgebra R N]

open MonoidalCategory in

noncomputable instance TensorProduct.instCoalgebra : Coalgebra R (M ⊗[R] N) :=
  let I := Monoidal.transport ((CoalgebraCat.comonEquivalence R).symm)
  CoalgEquiv.toCoalgebra
    (A := (CoalgebraCat.of R M ⊗ CoalgebraCat.of R N : CoalgebraCat R))
    { LinearEquiv.refl R _ with
      counit_comp := rfl
      map_comp_comul := by
        rw [CoalgebraCat.ofComonObjCoalgebraStruct_comul]
        simp [-Mon_.monMonoidalStruct_tensorObj_X,
          ModuleCat.MonoidalCategory.instMonoidalCategoryStruct_tensorHom,
          ModuleCat.comp_def, ModuleCat.of, ModuleCat.asHom,
          ModuleCat.MonoidalCategory.tensorμ_eq_tensorTensorTensorComm] }

end

namespace Coalgebra

namespace TensorProduct

open CoalgebraCat.MonoidalCategoryAux MonoidalCategory

variable {R M N P Q : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q] [Module R M] [Module R N]
  [Module R P] [Module R Q] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P] [Coalgebra R Q]

attribute [local instance] CoalgebraCat.instMonoidalCategoryAux in
section

noncomputable def map (f : M →ₗc[R] N) (g : P →ₗc[R] Q) :
    M ⊗[R] P →ₗc[R] N ⊗[R] Q where
  toLinearMap := _root_.TensorProduct.map f.toLinearMap g.toLinearMap
  counit_comp := by
    simp_rw [← tensorHom_toLinearMap]
    apply (CoalgebraCat.ofHom f ⊗ CoalgebraCat.ofHom g).1.counit_comp
  map_comp_comul := by
    simp_rw [← tensorHom_toLinearMap, ← comul_tensorObj]
    apply (CoalgebraCat.ofHom f ⊗ CoalgebraCat.ofHom g).1.map_comp_comul

variable (R M N P)

protected noncomputable def assoc :
    (M ⊗[R] N) ⊗[R] P ≃ₗc[R] M ⊗[R] (N ⊗[R] P) :=
  { _root_.TensorProduct.assoc R M N P with
    counit_comp := by
      simp_rw [← associator_hom_toLinearMap, ← counit_tensorObj_tensorObj_right,
        ← counit_tensorObj_tensorObj_left]
      apply CoalgHom.counit_comp (α_ (CoalgebraCat.of R M) (CoalgebraCat.of R N)
        (CoalgebraCat.of R P)).hom.1
    map_comp_comul := by
      simp_rw [← associator_hom_toLinearMap, ← comul_tensorObj_tensorObj_left,
        ← comul_tensorObj_tensorObj_right]
      exact CoalgHom.map_comp_comul (α_ (CoalgebraCat.of R M)
        (CoalgebraCat.of R N) (CoalgebraCat.of R P)).hom.1 }

variable {R M N P}

variable (R M)

protected noncomputable def lid : R ⊗[R] M ≃ₗc[R] M :=
  { _root_.TensorProduct.lid R M with
    counit_comp := by
      simp only [← leftUnitor_hom_toLinearMap]
      apply CoalgHom.counit_comp (λ_ (CoalgebraCat.of R M)).hom.1
    map_comp_comul := by
      simp_rw [← leftUnitor_hom_toLinearMap, ← comul_tensorObj]
      apply CoalgHom.map_comp_comul (λ_ (CoalgebraCat.of R M)).hom.1 }

variable {R M}

variable (R M)

protected noncomputable def rid : M ⊗[R] R ≃ₗc[R] M :=
  { _root_.TensorProduct.rid R M with
    counit_comp := by
      simp only [← rightUnitor_hom_toLinearMap]
      apply CoalgHom.counit_comp (ρ_ (CoalgebraCat.of R M)).hom.1
    map_comp_comul := by
      simp_rw [← rightUnitor_hom_toLinearMap, ← comul_tensorObj]
      apply CoalgHom.map_comp_comul (ρ_ (CoalgebraCat.of R M)).hom.1 }

variable {R M}

end

end TensorProduct

end Coalgebra

namespace CoalgHom

variable {R M N P : Type u} [CommRing R]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [Module R M] [Module R N]
  [Module R P] [Coalgebra R M] [Coalgebra R N] [Coalgebra R P]

variable (M)

noncomputable abbrev lTensor (f : N →ₗc[R] P) : M ⊗[R] N →ₗc[R] M ⊗[R] P :=
  Coalgebra.TensorProduct.map (CoalgHom.id R M) f

noncomputable abbrev rTensor (f : N →ₗc[R] P) : N ⊗[R] M →ₗc[R] P ⊗[R] M :=
  Coalgebra.TensorProduct.map f (CoalgHom.id R M)

end CoalgHom
