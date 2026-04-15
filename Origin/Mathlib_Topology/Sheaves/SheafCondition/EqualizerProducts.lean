/-
Extracted from Topology/Sheaves/SheafCondition/EqualizerProducts.lean
Genuine: 25 of 29 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.Topology.Sheaves.SheafCondition.PairwiseIntersections

/-!
# The sheaf condition in terms of an equalizer of products

Here we set up the machinery for the "usual" definition of the sheaf condition,
e.g. as in https://stacks.math.columbia.edu/tag/0072
in terms of an equalizer diagram where the two objects are
`∏ᶜ F.obj (U i)` and `∏ᶜ F.obj (U i) ⊓ (U j)`.

We show that this sheaf condition is equivalent to the "pairwise intersections" sheaf condition when
the presheaf is valued in a category with products, and thereby equivalent to the default sheaf
condition.
-/

universe v' v u

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalSpace.Opens

namespace TopCat

variable {C : Type u} [Category.{v} C] [HasProducts.{v'} C]

variable {X : TopCat.{v'}} (F : Presheaf C X) {ι : Type v'} (U : ι → Opens X)

namespace Presheaf

namespace SheafConditionEqualizerProducts

def piOpens : C :=
  ∏ᶜ fun i : ι => F.obj (op (U i))

def piInters : C :=
  ∏ᶜ fun p : ι × ι => F.obj (op (U p.1 ⊓ U p.2))

def leftRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.1 ≫ F.map (infLELeft (U p.1) (U p.2)).op

def rightRes : piOpens F U ⟶ piInters.{v'} F U :=
  Pi.lift fun p : ι × ι => Pi.π _ p.2 ≫ F.map (infLERight (U p.1) (U p.2)).op

def res : F.obj (op (iSup U)) ⟶ piOpens.{v'} F U :=
  Pi.lift fun i : ι => F.map (TopologicalSpace.Opens.leSupr U i).op

@[simp, elementwise]
theorem res_π (i : ι) : res F U ≫ limit.π _ ⟨i⟩ = F.map (Opens.leSupr U i).op := by
  rw [res, limit.lift_π, Fan.mk_π_app]

@[elementwise]
theorem w : res F U ≫ leftRes F U = res F U ≫ rightRes F U := by
  dsimp [res, leftRes, rightRes]
  -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
  refine limit.hom_ext (fun _ => ?_)
  simp only [limit.lift_π, limit.lift_π_assoc, Fan.mk_π_app, Category.assoc]
  rw [← F.map_comp]
  rw [← F.map_comp]
  congr 1

abbrev diagram : WalkingParallelPair ⥤ C :=
  parallelPair (leftRes.{v'} F U) (rightRes F U)

def fork : Fork.{v} (leftRes F U) (rightRes F U) :=
  Fork.ofι _ (w F U)

@[simp]
theorem fork_pt : (fork F U).pt = F.obj (op (iSup U)) :=
  rfl

@[simp]
theorem fork_ι : (fork F U).ι = res F U :=
  rfl

@[simp]
theorem fork_π_app_walkingParallelPair_zero : (fork F U).π.app WalkingParallelPair.zero = res F U :=
  rfl

@[simp (high)]
theorem fork_π_app_walkingParallelPair_one :
    (fork F U).π.app WalkingParallelPair.one = res F U ≫ leftRes F U :=
  rfl

variable {F} {G : Presheaf C X}

@[simp]
def piOpens.isoOfIso (α : F ≅ G) : piOpens F U ≅ piOpens.{v'} G U :=
  Pi.mapIso fun _ => α.app _

@[simp]
def piInters.isoOfIso (α : F ≅ G) : piInters F U ≅ piInters.{v'} G U :=
  Pi.mapIso fun _ => α.app _

def diagram.isoOfIso (α : F ≅ G) : diagram F U ≅ diagram.{v'} G U :=
  NatIso.ofComponents (by
    rintro ⟨⟩
    · exact piOpens.isoOfIso U α
    · exact piInters.isoOfIso U α)
    (by
      rintro ⟨⟩ ⟨⟩ ⟨⟩
      · simp
      · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
        refine limit.hom_ext (fun _ => ?_)
        simp only [leftRes, piOpens.isoOfIso, piInters.isoOfIso, parallelPair_map_left,
          Functor.mapIso_hom, lim_map, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
        refine limit.hom_ext (fun _ => ?_)
        simp only [rightRes, piOpens.isoOfIso, piInters.isoOfIso, parallelPair_map_right,
          Functor.mapIso_hom, lim_map, limit.lift_map, limit.lift_π, Cones.postcompose_obj_π,
          NatTrans.comp_app, Fan.mk_π_app, Discrete.natIso_hom_app, Iso.app_hom, Category.assoc,
          NatTrans.naturality, limMap_π_assoc]
      · simp)

def fork.isoOfIso (α : F ≅ G) :
    fork F U ≅ (Cones.postcompose (diagram.isoOfIso U α).inv).obj (fork G U) := by
  fapply Fork.ext
  · apply α.app
  · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
    refine limit.hom_ext (fun _ => ?_)
    dsimp only [Fork.ι]
    -- Ugh, `simp` can't unfold abbreviations.
    simp only [res, diagram.isoOfIso, Iso.app_hom, piOpens.isoOfIso, Cones.postcompose_obj_π,
      NatTrans.comp_app, fork_π_app_walkingParallelPair_zero, NatIso.ofComponents_inv_app,
      Functor.mapIso_inv, lim_map, limit.lift_map, Category.assoc, limit.lift_π, Fan.mk_π_app,
      Discrete.natIso_inv_app, Iso.app_inv, NatTrans.naturality, Iso.hom_inv_id_app_assoc]

end SheafConditionEqualizerProducts

def IsSheafEqualizerProducts (F : Presheaf.{v', v, u} C X) : Prop :=
  ∀ ⦃ι : Type v'⦄ (U : ι → Opens X), Nonempty (IsLimit (SheafConditionEqualizerProducts.fork F U))

/-!
The remainder of this file shows that the "equalizer products" sheaf condition is equivalent
to the "pairwise intersections" sheaf condition.
-/

namespace SheafConditionPairwiseIntersections

open CategoryTheory.Pairwise CategoryTheory.Pairwise.Hom

@[simps]
def coneEquivFunctorObj (c : Cone ((diagram U).op ⋙ F)) :
    Cone (SheafConditionEqualizerProducts.diagram F U) where
  pt := c.pt
  π :=
    { app := fun Z =>
        WalkingParallelPair.casesOn Z (Pi.lift fun i : ι => c.π.app (op (single i)))
          (Pi.lift fun b : ι × ι => c.π.app (op (pair b.1 b.2)))
      naturality := fun Y Z f => by
        cases Y <;> cases Z <;> cases f
        · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
          refine limit.hom_ext fun i => ?_
          dsimp
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app, CategoryTheory.Functor.map_id,
            Category.assoc]
          dsimp
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app]
        · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
          refine limit.hom_ext fun ⟨i, j⟩ => ?_
          dsimp [SheafConditionEqualizerProducts.leftRes]
          simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
            Category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (Hom.left i j))
          dsimp at h
          simpa using h
        · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
          refine limit.hom_ext fun ⟨i, j⟩ => ?_
          dsimp [SheafConditionEqualizerProducts.rightRes]
          simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
            Category.assoc]
          have h := c.π.naturality (Quiver.Hom.op (Hom.right i j))
          dsimp at h
          simpa using h
        · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
          refine limit.hom_ext fun i => ?_
          dsimp
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app, CategoryTheory.Functor.map_id,
            Category.assoc]
          dsimp
          simp only [limit.lift_π, Category.id_comp, Fan.mk_π_app] }

section

@[simps!]
def coneEquivFunctor :
    Limits.Cone ((diagram U).op ⋙ F) ⥤
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  obj c := coneEquivFunctorObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := fun j => by
        cases j <;>
          · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
            refine limit.hom_ext fun i => ?_
            simp only [Limits.Fan.mk_π_app, Limits.ConeMorphism.w, Limits.limit.lift_π,
              Category.assoc, coneEquivFunctorObj_π_app] }

end

@[simps]
def coneEquivInverseObj (c : Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :
    Limits.Cone ((diagram U).op ⋙ F) where
  pt := c.pt
  π :=
    { app := by
        intro x
        induction x using Opposite.rec' with | h x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · exact c.π.app WalkingParallelPair.zero ≫ Pi.π _ i
        · exact c.π.app WalkingParallelPair.one ≫ Pi.π _ (i, j)
      naturality := by
        intro x y f
        induction x using Opposite.rec' with | h x => ?_
        induction y using Opposite.rec' with | h y => ?_
        have ef : f = f.unop.op := rfl
        revert ef
        generalize f.unop = f'
        rintro rfl
        rcases x with (⟨i⟩ | ⟨⟩) <;> rcases y with (⟨⟩ | ⟨j, j⟩) <;> rcases f' with ⟨⟩
        · dsimp
          rw [F.map_id]
          simp
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.left
          dsimp [SheafConditionEqualizerProducts.leftRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (i, j)
          rw [h']
          simp only [Category.assoc, limit.lift_π, Fan.mk_π_app]
          rfl
        · dsimp
          simp only [Category.id_comp, Category.assoc]
          have h := c.π.naturality WalkingParallelPairHom.right
          dsimp [SheafConditionEqualizerProducts.rightRes] at h
          simp only [Category.id_comp] at h
          have h' := h =≫ Pi.π _ (j, i)
          rw [h']
          simp
          rfl
        · dsimp
          rw [F.map_id]
          simp }

@[simps!]
def coneEquivInverse :
    Limits.Cone (SheafConditionEqualizerProducts.diagram F U) ⥤
      Limits.Cone ((diagram U).op ⋙ F) where
  obj c := coneEquivInverseObj F U c
  map {c c'} f :=
    { hom := f.hom
      w := by
        intro x
        induction x using Opposite.rec' with | h x => ?_
        rcases x with (⟨i⟩ | ⟨i, j⟩)
        · dsimp
          dsimp only [Fork.ι]
          rw [← f.w WalkingParallelPair.zero, Category.assoc]
        · dsimp
          rw [← f.w WalkingParallelPair.one, Category.assoc] }

@[simps]
def coneEquivUnitIsoApp (c : Cone ((diagram U).op ⋙ F)) :
    (𝟭 (Cone ((diagram U).op ⋙ F))).obj c ≅
      (coneEquivFunctor F U ⋙ coneEquivInverse F U).obj c where
  hom :=
    { hom := 𝟙 _
      w := fun j => by
        induction j using Opposite.rec' with | h j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
  inv :=
    { hom := 𝟙 _
      w := fun j => by
        induction j using Opposite.rec' with | h j => ?_
        rcases j with ⟨⟩ <;>
        · dsimp [coneEquivInverse]
          simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }

@[simps!]
def coneEquivUnitIso :
    𝟭 (Limits.Cone ((diagram U).op ⋙ F)) ≅ coneEquivFunctor F U ⋙ coneEquivInverse F U :=
  NatIso.ofComponents (coneEquivUnitIsoApp F U)

@[simps!]
def coneEquivCounitIso :
    coneEquivInverse F U ⋙ coneEquivFunctor F U ≅
      𝟭 (Limits.Cone (SheafConditionEqualizerProducts.diagram F U)) :=
  NatIso.ofComponents
    (fun c =>
      { hom :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
                refine limit.hom_ext fun ⟨j⟩ => ?_
                dsimp [coneEquivInverse]
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π]
              · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
                refine limit.hom_ext fun ⟨i, j⟩ => ?_
                dsimp [coneEquivInverse]
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] }
        inv :=
          { hom := 𝟙 _
            w := by
              rintro ⟨_ | _⟩
              · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
                refine limit.hom_ext fun ⟨j⟩ => ?_
                dsimp [coneEquivInverse]
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π]
              · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
                refine limit.hom_ext fun ⟨i, j⟩ => ?_
                dsimp [coneEquivInverse]
                simp only [Limits.Fan.mk_π_app, Category.id_comp, Limits.limit.lift_π] } })
    fun {c d} f => by
    ext
    dsimp
    simp only [Category.comp_id, Category.id_comp]

@[simps]
def coneEquiv :
    Limits.Cone ((diagram U).op ⋙ F) ≌
      Limits.Cone (SheafConditionEqualizerProducts.diagram F U) where
  functor := coneEquivFunctor F U
  inverse := coneEquivInverse F U
  unitIso := coneEquivUnitIso F U
  counitIso := coneEquivCounitIso F U

def isLimitMapConeOfIsLimitSheafConditionFork
    (P : IsLimit (SheafConditionEqualizerProducts.fork F U)) : IsLimit (F.mapCone (cocone U).op) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U).symm).symm P)
    { hom :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | h x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            intro x
            induction x with | h x => ?_
            rcases x with ⟨⟩
            · simp
              rfl
            · dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

def isLimitSheafConditionForkOfIsLimitMapCone (Q : IsLimit (F.mapCone (cocone U).op)) :
    IsLimit (SheafConditionEqualizerProducts.fork F U) :=
  IsLimit.ofIsoLimit ((IsLimit.ofConeEquiv (coneEquiv F U)).symm Q)
    { hom :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
              refine limit.hom_ext fun ⟨i, j⟩ => ?_
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl }
      inv :=
        { hom := 𝟙 _
          w := by
            rintro ⟨⟩
            · simp
              rfl
            · -- Porting note (https://github.com/leanprover-community/mathlib4/issues/11041): `ext` can't see `limit.hom_ext` applies here:
              refine limit.hom_ext fun ⟨i, j⟩ => ?_
              dsimp [coneEquivInverse, SheafConditionEqualizerProducts.res,
                SheafConditionEqualizerProducts.leftRes]
              simp only [limit.lift_π, limit.lift_π_assoc, Category.id_comp, Fan.mk_π_app,
                Category.assoc]
              rw [← F.map_comp]
              rfl } }

end SheafConditionPairwiseIntersections

open SheafConditionPairwiseIntersections

theorem isSheaf_iff_isSheafEqualizerProducts (F : Presheaf C X) :
    F.IsSheaf ↔ F.IsSheafEqualizerProducts :=
  (isSheaf_iff_isSheafPairwiseIntersections F).trans <|
    Iff.intro (fun h _ U => ⟨isLimitSheafConditionForkOfIsLimitMapCone F U (h U).some⟩) fun h _ U =>
      ⟨isLimitMapConeOfIsLimitSheafConditionFork F U (h U).some⟩

end Presheaf

end TopCat
