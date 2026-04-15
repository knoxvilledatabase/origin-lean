/-
Extracted from Topology/Sheaves/SheafCondition/UniqueGluing.lean
Genuine: 13 of 13 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The sheaf condition in terms of unique gluings

We provide an alternative formulation of the sheaf condition in terms of unique gluings.

We work with sheaves valued in a concrete category `C` admitting all limits, whose forgetful
functor `C ⥤ Type` preserves limits and reflects isomorphisms. The usual categories of algebraic
structures, such as `MonCat`, `AddCommGrpCat`, `RingCat`, `CommRingCat` etc. are all examples of
this kind of category.

A presheaf `F : Presheaf C X` satisfies the sheaf condition if and only if, for every
compatible family of sections `sf : Π i : ι, F.obj (op (U i))`, there exists a unique gluing
`s : F.obj (op (iSup U))`.

Here, the family `sf` is called compatible, if for all `i j : ι`, the restrictions of `sf i`
and `sf j` to `U i ⊓ U j` agree. A section `s : F.obj (op (iSup U))` is a gluing for the
family `sf`, if `s` restricts to `sf i` on `U i` for all `i : ι`

We show that the sheaf condition in terms of unique gluings is equivalent to the definition
in terms of pairwise intersections. Our approach is as follows: First, we show them to be equivalent
for `Type`-valued presheaves. Then we use that composing a presheaf with a limit-preserving and
isomorphism-reflecting functor leaves the sheaf condition invariant, as shown in
`Mathlib/Topology/Sheaves/Forget.lean`.

-/

noncomputable section

open TopCat TopCat.Presheaf CategoryTheory CategoryTheory.Limits

  TopologicalSpace TopologicalSpace.Opens Opposite

universe x

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace TopCat

namespace Presheaf

variable {X : TopCat.{x}} (F : Presheaf C X) {ι : Type*} (U : ι → Opens X)

def IsCompatible (sf : ∀ i : ι, ToType (F.obj (op (U i)))) : Prop :=
  ∀ i j : ι, F.map (infLELeft (U i) (U j)).op (sf i) = F.map (infLERight (U i) (U j)).op (sf j)

def IsGluing (sf : ∀ i : ι, ToType (F.obj (op (U i)))) (s : ToType (F.obj (op (iSup U)))) : Prop :=
  ∀ i : ι, F.map (Opens.leSupr U i).op s = sf i

def IsSheafUniqueGluing : Prop :=
  ∀ ⦃ι : Type x⦄ (U : ι → Opens X) (sf : ∀ i : ι, ToType (F.obj (op (U i)))),
    IsCompatible F U sf → ∃! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s

end

section TypeValued

variable {X : TopCat.{x}} {F : Presheaf Type* X} {ι : Type*} {U : ι → Opens X}

def objPairwiseOfFamily (sf : ∀ i, F.obj (op (U i))) :
    ∀ i, ((Pairwise.diagram U).op ⋙ F).obj i
  | ⟨Pairwise.single i⟩ => sf i
  | ⟨Pairwise.pair i j⟩ => F.map (infLELeft (U i) (U j)).op (sf i)

def IsCompatible.sectionPairwise {sf} (h : IsCompatible F U sf) :
    ((Pairwise.diagram U).op ⋙ F).sections := by
  refine ⟨objPairwiseOfFamily sf, ?_⟩
  let G := (Pairwise.diagram U).op ⋙ F
  rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) (_ | _ | _ | _)
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.single i) _
  · rfl
  · exact (h i' i).symm
  · exact ConcreteCategory.congr_hom (G.map_id <| op <| Pairwise.pair i j) _

theorem isGluing_iff_pairwise {sf s} : IsGluing F U sf s ↔
    ∀ i, (F.mapCone (Pairwise.cocone U).op).π.app i s = objPairwiseOfFamily sf i := by
  refine ⟨fun h ↦ ?_, fun h i ↦ h (op <| Pairwise.single i)⟩
  rintro (i | ⟨i, j⟩)
  · exact h i
  · rw [← (F.mapCone (Pairwise.cocone U).op).w (op <| Pairwise.Hom.left i j)]
    exact congr_arg _ (h i)

theorem IsSheaf.isSheafUniqueGluing_types (h : F.IsSheaf) (sf : ∀ i : ι, F.obj (op (U i)))
    (cpt : IsCompatible F U sf) : ∃! s : F.obj (op (iSup U)), IsGluing F U sf s := by
  simp_rw [isGluing_iff_pairwise]
  exact (Types.isLimit_iff _).mp (h.isSheafPairwiseIntersections U) _ cpt.sectionPairwise.prop

variable (F)

set_option backward.isDefEq.respectTransparency false in

theorem isSheaf_iff_isSheafUniqueGluing_types : F.IsSheaf ↔ F.IsSheafUniqueGluing := by
  simp_rw [isSheaf_iff_isSheafPairwiseIntersections, IsSheafPairwiseIntersections,
    Types.isLimit_iff, IsSheafUniqueGluing, isGluing_iff_pairwise]
  refine forall₂_congr fun ι U ↦ ⟨fun h sf cpt ↦ ?_, fun h s hs ↦ ?_⟩
  · exact h _ cpt.sectionPairwise.prop
  · specialize h (fun i ↦ s <| op <| Pairwise.single i) fun i j ↦
      (hs <| op <| Pairwise.Hom.left i j).trans (hs <| op <| Pairwise.Hom.right i j).symm
    convert h; ext (i | ⟨i, j⟩)
    · rfl
    · exact (hs <| op <| Pairwise.Hom.left i j).symm

theorem isSheaf_of_isSheafUniqueGluing_types (Fsh : F.IsSheafUniqueGluing) : F.IsSheaf :=
  (isSheaf_iff_isSheafUniqueGluing_types F).mpr Fsh

end TypeValued

variable [HasLimitsOfSize.{x, x} C] [(forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{x, x} (forget C)]

variable {X : TopCat.{x}} {F : Presheaf C X}

theorem IsSheaf.isSheafUniqueGluing (h : F.IsSheaf) {ι : Type*} (U : ι → Opens X)
    (sf : ∀ i : ι, ToType (F.obj (op (U i))))
    (cpt : IsCompatible F U sf) : ∃! s : ToType (F.obj (op (iSup U))), IsGluing F U sf s :=
  ((isSheaf_iff_isSheaf_comp' (forget C) F).mp h).isSheafUniqueGluing_types sf cpt

variable (F)

theorem isSheaf_iff_isSheafUniqueGluing : F.IsSheaf ↔ F.IsSheafUniqueGluing :=
  Iff.trans (isSheaf_iff_isSheaf_comp' (forget C) F)
    (isSheaf_iff_isSheafUniqueGluing_types (F ⋙ forget C))

end

end Presheaf

namespace Sheaf

open Presheaf CategoryTheory

variable [HasLimitsOfSize.{x, x} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]

variable [PreservesLimitsOfSize.{x, x} (CategoryTheory.forget C)]

variable {X : TopCat.{x}} (F : Sheaf C X) {ι : Type*} (U : ι → Opens X)

theorem existsUnique_gluing (sf : ∀ i : ι, ToType (F.1.obj (op (U i))))
    (h : IsCompatible F.1 U sf) :
    ∃! s : ToType (F.1.obj (op (iSup U))), IsGluing F.1 U sf s :=
  IsSheaf.isSheafUniqueGluing F.property U sf h

theorem existsUnique_gluing' (V : Opens X) (iUV : ∀ i : ι, U i ⟶ V) (hcover : V ≤ iSup U)
    (sf : ∀ i : ι, ToType (F.1.obj (op (U i)))) (h : IsCompatible F.1 U sf) :
    ∃! s : ToType (F.1.obj (op V)), ∀ i : ι, F.1.map (iUV i).op s = sf i := by
  have V_eq_supr_U : V = iSup U := le_antisymm hcover (iSup_le fun i => (iUV i).le)
  obtain ⟨gl, gl_spec, gl_uniq⟩ := F.existsUnique_gluing U sf h
  refine ⟨F.1.map (eqToHom V_eq_supr_U).op gl, ?_, ?_⟩
  · intro i
    rw [← ConcreteCategory.comp_apply, ← F.1.map_comp]
    exact gl_spec i
  · intro gl' gl'_spec
    convert congr_arg _ (gl_uniq (F.1.map (eqToHom V_eq_supr_U.symm).op gl') fun i => _) <;>
      rw [← ConcreteCategory.comp_apply, ← F.1.map_comp]
    · simp
    · exact gl'_spec i
