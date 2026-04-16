/-
Extracted from RepresentationTheory/FDRep.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.Algebra.Category.FGModuleCat.Limits
import Mathlib.CategoryTheory.Monoidal.Rigid.Braided
import Mathlib.CategoryTheory.Preadditive.Schur
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Rep

noncomputable section

/-!
# `FDRep k G` is the category of finite dimensional `k`-linear representations of `G`.

If `V : FDRep k G`, there is a coercion that allows you to treat `V` as a type,
and this type comes equipped with `Module k V` and `FiniteDimensional k V` instances.
Also `V.ρ` gives the homomorphism `G →* (V →ₗ[k] V)`.

Conversely, given a homomorphism `ρ : G →* (V →ₗ[k] V)`,
you can construct the bundled representation as `Rep.of ρ`.

We prove Schur's Lemma: the dimension of the `Hom`-space between two irreducible representation is
`0` if they are not isomorphic, and `1` if they are.
This is the content of `finrank_hom_simple_simple`

We verify that `FDRep k G` is a `k`-linear monoidal category, and rigid when `G` is a group.

`FDRep k G` has all finite limits.

## TODO
* `FdRep k G ≌ FullSubcategory (FiniteDimensional k)`
* `FdRep k G` has all finite colimits.
* `FdRep k G` is abelian.
* `FdRep k G ≌ FGModuleCat (MonoidAlgebra k G)`.

-/

universe u

open CategoryTheory

open CategoryTheory.Limits

abbrev FDRep (k G : Type u) [Field k] [Monoid G] :=
  Action (FGModuleCat.{u} k) (MonCat.of G)

alias FdRep := FDRep

namespace FDRep

variable {k G : Type u} [Field k] [Monoid G]

instance : LargeCategory (FDRep k G) := inferInstance

instance : ConcreteCategory (FDRep k G) := inferInstance

instance : Preadditive (FDRep k G) := inferInstance

instance : HasFiniteLimits (FDRep k G) := inferInstance

instance : Linear k (FDRep k G) := by infer_instance

instance : CoeSort (FDRep k G) (Type u) :=
  ConcreteCategory.hasCoeToSort _

instance (V : FDRep k G) : AddCommGroup V := by
  change AddCommGroup ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : Module k V := by
  change Module k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V).obj; infer_instance

instance (V : FDRep k G) : FiniteDimensional k V := by
  change FiniteDimensional k ((forget₂ (FDRep k G) (FGModuleCat k)).obj V); infer_instance

instance (V W : FDRep k G) : FiniteDimensional k (V ⟶ W) :=
  FiniteDimensional.of_injective ((forget₂ (FDRep k G) (FGModuleCat k)).mapLinearMap k)
    (Functor.map_injective (forget₂ (FDRep k G) (FGModuleCat k)))

def ρ (V : FDRep k G) : G →* V →ₗ[k] V :=
  Action.ρ V

def isoToLinearEquiv {V W : FDRep k G} (i : V ≅ W) : V ≃ₗ[k] W :=
  FGModuleCat.isoToLinearEquiv ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)

theorem Iso.conj_ρ {V W : FDRep k G} (i : V ≅ W) (g : G) :
    W.ρ g = (FDRep.isoToLinearEquiv i).conj (V.ρ g) := by
  -- Porting note: Changed `rw` to `erw`
  erw [FDRep.isoToLinearEquiv, ← FGModuleCat.Iso.conj_eq_conj, Iso.conj_apply]
  rw [Iso.eq_inv_comp ((Action.forget (FGModuleCat k) (MonCat.of G)).mapIso i)]
  exact (i.hom.comm g).symm

@[simps ρ]
def of {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) : FDRep k G :=
  ⟨FGModuleCat.of k V, ρ⟩

instance : HasForget₂ (FDRep k G) (Rep k G) where
  forget₂ := (forget₂ (FGModuleCat k) (ModuleCat k)).mapAction (MonCat.of G)

theorem forget₂_ρ (V : FDRep k G) : ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ = V.ρ := by
  ext g v; rfl

example : MonoidalCategory (FDRep k G) := by infer_instance

example : MonoidalPreadditive (FDRep k G) := by infer_instance

example : MonoidalLinear k (FDRep k G) := by infer_instance

open Module

open scoped Classical

instance : HasKernels (FDRep k G) := by infer_instance

theorem finrank_hom_simple_simple [IsAlgClosed k] (V W : FDRep k G) [Simple V] [Simple W] :
    finrank k (V ⟶ W) = if Nonempty (V ≅ W) then 1 else 0 :=
  CategoryTheory.finrank_hom_simple_simple k V W

end FDRep

namespace FDRep

variable {k G : Type u} [Field k] [Group G]

noncomputable instance : RightRigidCategory (FDRep k G) := by
  change RightRigidCategory (Action (FGModuleCat k) (Grp.of G)); infer_instance

example : RigidCategory (FDRep k G) := by infer_instance

end FDRep

namespace FDRep

open Representation

variable {k G V : Type u} [Field k] [Group G]

variable [AddCommGroup V] [Module k V]

variable [FiniteDimensional k V]

variable (ρV : Representation k G V) (W : FDRep k G)

open scoped MonoidalCategory

noncomputable def dualTensorIsoLinHomAux :
    (FDRep.of ρV.dual ⊗ W).V ≅ (FDRep.of (linHom ρV W.ρ)).V :=
  -- Porting note: had to make all types explicit arguments
  @LinearEquiv.toFGModuleCatIso k _ (FDRep.of ρV.dual ⊗ W).V (V →ₗ[k] W)
    _ _ _ _ _ _ (dualTensorHomEquiv k V W)

noncomputable def dualTensorIsoLinHom : FDRep.of ρV.dual ⊗ W ≅ FDRep.of (linHom ρV W.ρ) := by
  refine Action.mkIso (dualTensorIsoLinHomAux ρV W) ?_
  convert dualTensorHom_comm ρV W.ρ

end FDRep
