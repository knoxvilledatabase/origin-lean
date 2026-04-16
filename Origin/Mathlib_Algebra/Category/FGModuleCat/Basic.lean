/-
Extracted from Algebra/Category/FGModuleCat/Basic.lean
Genuine: 14 | Conflates: 0 | Dissolved: 0 | Infrastructure: 35
-/
import Origin.Core
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
import Mathlib.CategoryTheory.Monoidal.Subcategory
import Mathlib.LinearAlgebra.Coevaluation
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.RingTheory.Finiteness.TensorProduct

noncomputable section

/-!
# The category of finitely generated modules over a ring

This introduces `FGModuleCat R`, the category of finitely generated modules over a ring `R`.
It is implemented as a full subcategory on a subtype of `ModuleCat R`.

When `K` is a field,
`FGModuleCatCat K` is the category of finite dimensional vector spaces over `K`.

We first create the instance as a preadditive category.
When `R` is commutative we then give the structure as an `R`-linear monoidal category.
When `R` is a field we give it the structure of a closed monoidal category
and then as a right-rigid monoidal category.

## Future work

* Show that `FGModuleCat R` is abelian when `R` is (left)-noetherian.

-/

noncomputable section

open CategoryTheory ModuleCat.monoidalCategory

universe u

section Ring

variable (R : Type u) [Ring R]

def FGModuleCat :=
  FullSubcategory fun V : ModuleCat.{u} R => Module.Finite R V

variable {R}

def FGModuleCat.carrier (M : FGModuleCat R) : Type u := M.obj.carrier

instance : CoeSort (FGModuleCat R) (Type u) :=
  ⟨FGModuleCat.carrier⟩

attribute [coe] FGModuleCat.carrier

instance (M : FGModuleCat R) : AddCommGroup M := by
  change AddCommGroup M.obj
  infer_instance

instance (M : FGModuleCat R) : Module R M := by
  change Module R M.obj
  infer_instance

instance : LargeCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance {M N : FGModuleCat R} : FunLike (M ⟶ N) M N :=
  LinearMap.instFunLike

instance {M N : FGModuleCat R} : LinearMapClass (M ⟶ N) R M N :=
  LinearMap.semilinearMapClass

instance : ConcreteCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : Preadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

end Ring

namespace FGModuleCat

section Ring

variable (R : Type u) [Ring R]

instance finite (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : Inhabited (FGModuleCat R) :=
  ⟨⟨ModuleCat.of R R, Module.Finite.self R⟩⟩

def of (V : Type u) [AddCommGroup V] [Module R V] [Module.Finite R V] : FGModuleCat R :=
  ⟨ModuleCat.of R V, by change Module.Finite R V; infer_instance⟩

instance (V : FGModuleCat R) : Module.Finite R V :=
  V.property

instance : HasForget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : (forget₂ (FGModuleCat R) (ModuleCat.{u} R)).Full where
  map_surjective f := ⟨f, rfl⟩

variable {R}

def isoToLinearEquiv {V W : FGModuleCat R} (i : V ≅ W) : V ≃ₗ[R] W :=
  ((forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).mapIso i).toLinearEquiv

@[simps]
def _root_.LinearEquiv.toFGModuleCatIso
    {V W : Type u} [AddCommGroup V] [Module R V] [Module.Finite R V]
    [AddCommGroup W] [Module R W] [Module.Finite R W] (e : V ≃ₗ[R] W) :
    FGModuleCat.of R V ≅ FGModuleCat.of R W where
  hom := e.toLinearMap
  inv := e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.left_inv x
  inv_hom_id := by ext x; exact e.right_inv x

end Ring

section CommRing

variable (R : Type u) [CommRing R]

instance : Linear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance monoidalPredicate_module_finite :
    MonoidalCategory.MonoidalPredicate fun V : ModuleCat.{u} R => Module.Finite R V where
  prop_id := Module.Finite.self R
  prop_tensor := @fun X Y _ _ => Module.Finite.tensorProduct R X Y

instance instMonoidalCategory : MonoidalCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

open MonoidalCategory

instance : SymmetricCategory (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalPreadditive (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : MonoidalLinear R (FGModuleCat R) := by
  dsimp [FGModuleCat]
  infer_instance

instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Monoidal :=
  fullSubcategoryInclusionMonoidal _

instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Additive where

instance : (forget₂ (FGModuleCat.{u} R) (ModuleCat.{u} R)).Linear R where

end CommRing

section Field

variable (K : Type u) [Field K]

instance (V W : FGModuleCat K) : Module.Finite K (V ⟶ W) :=
  (by infer_instance : Module.Finite K (V →ₗ[K] W))

instance closedPredicateModuleFinite :
    MonoidalCategory.ClosedPredicate fun V : ModuleCat.{u} K ↦ Module.Finite K V where
  prop_ihom {X Y} _ _ := Module.Finite.linearMap K K X Y

instance : MonoidalClosed (FGModuleCat K) := by
  dsimp [FGModuleCat]
  -- Porting note (https://github.com/leanprover-community/mathlib4/pull/11187): was `infer_instance`
  exact MonoidalCategory.fullMonoidalClosedSubcategory
    (fun V : ModuleCat.{u} K => Module.Finite K V)

variable (V W : FGModuleCat K)

def FGModuleCatDual : FGModuleCat K :=
  ⟨ModuleCat.of K (Module.Dual K V), Subspace.instModuleDualFiniteDimensional⟩

open CategoryTheory.MonoidalCategory

def FGModuleCatCoevaluation : 𝟙_ (FGModuleCat K) ⟶ V ⊗ FGModuleCatDual K V :=
  coevaluation K V

theorem FGModuleCatCoevaluation_apply_one :
    FGModuleCatCoevaluation K V (1 : K) =
      ∑ i : Basis.ofVectorSpaceIndex K V,
        (Basis.ofVectorSpace K V) i ⊗ₜ[K] (Basis.ofVectorSpace K V).coord i :=
  coevaluation_apply_one K V

def FGModuleCatEvaluation : FGModuleCatDual K V ⊗ V ⟶ 𝟙_ (FGModuleCat K) :=
  contractLeft K V

@[simp]
theorem FGModuleCatEvaluation_apply (f : FGModuleCatDual K V) (x : V) :
    (FGModuleCatEvaluation K V) (f ⊗ₜ x) = f.toFun x :=
  contractLeft_apply f x

private theorem coevaluation_evaluation :
    letI V' : FGModuleCat K := FGModuleCatDual K V
    V' ◁ FGModuleCatCoevaluation K V ≫ (α_ V' V V').inv ≫ FGModuleCatEvaluation K V ▷ V' =
      (ρ_ V').hom ≫ (λ_ V').inv := by
  apply contractLeft_assoc_coevaluation K V

private theorem evaluation_coevaluation :
    FGModuleCatCoevaluation K V ▷ V ≫
        (α_ V (FGModuleCatDual K V) V).hom ≫ V ◁ FGModuleCatEvaluation K V =
      (λ_ V).hom ≫ (ρ_ V).inv := by
  apply contractLeft_assoc_coevaluation' K V

instance exactPairing : ExactPairing V (FGModuleCatDual K V) where
  coevaluation' := FGModuleCatCoevaluation K V
  evaluation' := FGModuleCatEvaluation K V
  coevaluation_evaluation' := coevaluation_evaluation K V
  evaluation_coevaluation' := evaluation_coevaluation K V

instance rightDual : HasRightDual V :=
  ⟨FGModuleCatDual K V⟩

instance rightRigidCategory : RightRigidCategory (FGModuleCat K) where

end Field

end FGModuleCat

/-!
`@[simp]` lemmas for `LinearMap.comp` and categorical identities.
-/

@[simp] theorem LinearMap.comp_id_fgModuleCat
    {R} [Ring R] {G : FGModuleCat.{u} R} {H : Type u} [AddCommGroup H] [Module R H]
    (f : G →ₗ[R] H) : f.comp (𝟙 G) = f :=
  Category.id_comp (ModuleCat.asHom f)

@[simp] theorem LinearMap.id_fgModuleCat_comp
    {R} [Ring R] {G : Type u} [AddCommGroup G] [Module R G] {H : FGModuleCat.{u} R}
    (f : G →ₗ[R] H) : LinearMap.comp (𝟙 H) f = f :=
  Category.comp_id (ModuleCat.asHom f)
