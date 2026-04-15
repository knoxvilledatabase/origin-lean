/-
Extracted from CategoryTheory/Limits/ConeCategory.lean
Genuine: 38 | Conflates: 0 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core
import Mathlib.CategoryTheory.Adjunction.Comma
import Mathlib.CategoryTheory.Comma.Over
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence

/-!
# Limits and the category of (co)cones

This files contains results that stem from the limit API. For the definition and the category
instance of `Cone`, please refer to `CategoryTheory/Limits/Cones.lean`.

## Main results
* The category of cones on `F : J ⥤ C` is equivalent to the category
  `CostructuredArrow (const J) F`.
* A cone is limiting iff it is terminal in the category of cones. As a corollary, an equivalence of
  categories of cones preserves limiting properties.

-/

namespace CategoryTheory.Limits

open CategoryTheory CategoryTheory.Functor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {J : Type u₁} [Category.{v₁} J] {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C] {D : Type u₄} [Category.{v₄} D]

@[simps]
def Cone.toStructuredArrow {F : J ⥤ C} (c : Cone F) : J ⥤ StructuredArrow c.pt F where
  obj j := StructuredArrow.mk (c.π.app j)
  map f := StructuredArrow.homMk f

@[simps]
noncomputable def limit.toStructuredArrow (F : J ⥤ C) [HasLimit F] :
    J ⥤ StructuredArrow (limit F) F where
  obj j := StructuredArrow.mk (limit.π F j)
  map f := StructuredArrow.homMk f

def Cone.toStructuredArrowIsoToStructuredArrow {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ≅ (𝟭 J).toStructuredArrow c.pt F c.π.app (by simp) :=
  Iso.refl _

def _root_.CategoryTheory.Functor.toStructuredArrowIsoToStructuredArrow (G : J ⥤ K) (X : C)
    (F : K ⥤ C) (f : (Y : J) → X ⟶ F.obj (G.obj Y))
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), f Y ≫ F.map (G.map g) = f Z) :
    G.toStructuredArrow X F f h ≅
      (Cone.mk X ⟨f, by simp [h]⟩).toStructuredArrow ⋙ StructuredArrow.pre _ _ _ :=
  Iso.refl _

@[simps!]
def Cone.toStructuredArrowCompProj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
lemma Cone.toStructuredArrow_comp_proj {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.proj _ _ = 𝟭 J :=
  rfl

@[simps!]
def Cone.toStructuredArrowCompToUnderCompForget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma Cone.toStructuredArrow_comp_toUnder_comp_forget {F : J ⥤ C} (c : Cone F) :
    c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _ ⋙ Under.forget _ = F :=
  rfl

@[simps]
def Cone.toUnder {F : J ⥤ C} (c : Cone F) :
    Cone (c.toStructuredArrow ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 c.pt)
  π := { app := fun j => Under.homMk (c.π.app j) (by simp) }

noncomputable def limit.toUnder (F : J ⥤ C) [HasLimit F] :
    Cone (limit.toStructuredArrow F ⋙ StructuredArrow.toUnder _ _) where
  pt := Under.mk (𝟙 (limit F))
  π := { app := fun j => Under.homMk (limit.π F j) (by simp) }

@[simps!]
def Cone.mapConeToUnder {F : J ⥤ C} (c : Cone F) : (Under.forget c.pt).mapCone c.toUnder ≅ c :=
  Iso.refl _

@[simps!]
def Cone.fromStructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ StructuredArrow X F) :
    Cone (G ⋙ StructuredArrow.proj X F ⋙ F) where
  π := { app := fun j => (G.obj j).hom }

@[simps]
def Cone.toStructuredArrowCone {K : J ⥤ C} (c : Cone K) (F : C ⥤ D) {X : D} (f : X ⟶ F.obj c.pt) :
    Cone ((F.mapCone c).toStructuredArrow ⋙ StructuredArrow.map f ⋙ StructuredArrow.pre _ K F) where
  pt := StructuredArrow.mk f
  π := { app := fun j => StructuredArrow.homMk (c.π.app j) rfl }

@[simps]
def Cone.toCostructuredArrow (F : J ⥤ C) : Cone F ⥤ CostructuredArrow (const J) F where
  obj c := CostructuredArrow.mk c.π
  map f := CostructuredArrow.homMk f.hom

@[simps]
def Cone.fromCostructuredArrow (F : J ⥤ C) : CostructuredArrow (const J) F ⥤ Cone F where
  obj c := ⟨c.left, c.hom⟩
  map f :=
    { hom := f.left
      w := fun j => by
        convert congr_fun (congr_arg NatTrans.app f.w) j
        dsimp
        simp }

@[simps]
def Cone.equivCostructuredArrow (F : J ⥤ C) : Cone F ≌ CostructuredArrow (const J) F where
  functor := Cone.toCostructuredArrow F
  inverse := Cone.fromCostructuredArrow F
  unitIso := NatIso.ofComponents Cones.eta
  counitIso := NatIso.ofComponents fun _ => (CostructuredArrow.eta _).symm

def Cone.isLimitEquivIsTerminal {F : J ⥤ C} (c : Cone F) : IsLimit c ≃ IsTerminal c :=
  IsLimit.isoUniqueConeMorphism.toEquiv.trans
    { toFun := fun _ => IsTerminal.ofUnique _
      invFun := fun h s => ⟨⟨IsTerminal.from h s⟩, fun a => IsTerminal.hom_ext h a _⟩
      left_inv := by aesop_cat
      right_inv := by aesop_cat }

theorem hasLimit_iff_hasTerminal_cone (F : J ⥤ C) : HasLimit F ↔ HasTerminal (Cone F) :=
  ⟨fun _ => (Cone.isLimitEquivIsTerminal _ (limit.isLimit F)).hasTerminal, fun h =>
    haveI : HasTerminal (Cone F) := h
    ⟨⟨⟨⊤_ _, (Cone.isLimitEquivIsTerminal _).symm terminalIsTerminal⟩⟩⟩⟩

theorem hasLimitsOfShape_iff_isLeftAdjoint_const :
    HasLimitsOfShape J C ↔ IsLeftAdjoint (const J : C ⥤ _) :=
  calc
    HasLimitsOfShape J C ↔ ∀ F : J ⥤ C, HasLimit F :=
      ⟨fun h => h.has_limit, fun h => HasLimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasTerminal (Cone F) := forall_congr' hasLimit_iff_hasTerminal_cone
    _ ↔ ∀ F : J ⥤ C, HasTerminal (CostructuredArrow (const J) F) :=
      (forall_congr' fun F => (Cone.equivCostructuredArrow F).hasTerminal_iff)
    _ ↔ (IsLeftAdjoint (const J : C ⥤ _)) :=
      isLeftAdjoint_iff_hasTerminal_costructuredArrow.symm

theorem IsLimit.liftConeMorphism_eq_isTerminal_from {F : J ⥤ C} {c : Cone F} (hc : IsLimit c)
    (s : Cone F) : hc.liftConeMorphism s = IsTerminal.from (Cone.isLimitEquivIsTerminal _ hc) _ :=
  rfl

theorem IsTerminal.from_eq_liftConeMorphism {F : J ⥤ C} {c : Cone F} (hc : IsTerminal c)
    (s : Cone F) :
    IsTerminal.from hc s = ((Cone.isLimitEquivIsTerminal _).symm hc).liftConeMorphism s :=
  (IsLimit.liftConeMorphism_eq_isTerminal_from (c.isLimitEquivIsTerminal.symm hc) s).symm

noncomputable def IsLimit.ofPreservesConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [PreservesLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit c) : IsLimit (G.obj c) :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalObj _ _

noncomputable def IsLimit.ofReflectsConeTerminal {F : J ⥤ C} {F' : K ⥤ D} (G : Cone F ⥤ Cone F')
    [ReflectsLimit (Functor.empty.{0} _) G] {c : Cone F} (hc : IsLimit (G.obj c)) : IsLimit c :=
  (Cone.isLimitEquivIsTerminal _).symm <| (Cone.isLimitEquivIsTerminal _ hc).isTerminalOfObj _ _

@[simps]
def Cocone.toCostructuredArrow {F : J ⥤ C} (c : Cocone F) : J ⥤ CostructuredArrow F c.pt where
  obj j := CostructuredArrow.mk (c.ι.app j)
  map f := CostructuredArrow.homMk f

@[simps]
noncomputable def colimit.toCostructuredArrow (F : J ⥤ C) [HasColimit F] :
    J ⥤ CostructuredArrow F (colimit F) where
  obj j := CostructuredArrow.mk (colimit.ι F j)
  map f := CostructuredArrow.homMk f

def Cocone.toCostructuredArrowIsoToCostructuredArrow {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ≅ (𝟭 J).toCostructuredArrow F c.pt c.ι.app (by simp) :=
  Iso.refl _

def _root_.CategoryTheory.Functor.toCostructuredArrowIsoToCostructuredArrow (G : J ⥤ K)
    (F : K ⥤ C) (X : C) (f : (Y : J) → F.obj (G.obj Y) ⟶ X)
    (h : ∀ {Y Z : J} (g : Y ⟶ Z), F.map (G.map g) ≫ f Z = f Y) :
    G.toCostructuredArrow F X f h ≅
      (Cocone.mk X ⟨f, by simp [h]⟩).toCostructuredArrow ⋙ CostructuredArrow.pre _ _ _ :=
  Iso.refl _

@[simps!]
def Cocone.toCostructuredArrowCompProj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ ≅ 𝟭 J :=
  Iso.refl _

@[simp]
lemma Cocone.toCostructuredArrow_comp_proj {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.proj _ _ = 𝟭 J :=
  rfl

@[simps!]
def Cocone.toCostructuredArrowCompToOverCompForget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma Cocone.toCostructuredArrow_comp_toOver_comp_forget {F : J ⥤ C} (c : Cocone F) :
    c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _ ⋙ Over.forget _ = F :=
  rfl

@[simps]
def Cocone.toOver {F : J ⥤ C} (c : Cocone F) :
    Cocone (c.toCostructuredArrow ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 c.pt)
  ι := { app := fun j => Over.homMk (c.ι.app j) (by simp) }

@[simps]
noncomputable def colimit.toOver (F : J ⥤ C) [HasColimit F] :
    Cocone (colimit.toCostructuredArrow F ⋙ CostructuredArrow.toOver _ _) where
  pt := Over.mk (𝟙 (colimit F))
  ι := { app := fun j => Over.homMk (colimit.ι F j) (by simp) }

@[simps!]
def Cocone.mapCoconeToOver {F : J ⥤ C} (c : Cocone F) : (Over.forget c.pt).mapCocone c.toOver ≅ c :=
  Iso.refl _

@[simps!]
def Cocone.fromCostructuredArrow (F : C ⥤ D) {X : D} (G : J ⥤ CostructuredArrow F X) :
    Cocone (G ⋙ CostructuredArrow.proj F X ⋙ F) where
  ι := { app := fun j => (G.obj j).hom }

@[simps]
def Cocone.toCostructuredArrowCocone {K : J ⥤ C} (c : Cocone K) (F : C ⥤ D) {X : D}
    (f : F.obj c.pt ⟶ X) : Cocone ((F.mapCocone c).toCostructuredArrow ⋙
      CostructuredArrow.map f ⋙ CostructuredArrow.pre _ _ _) where
  pt := CostructuredArrow.mk f
  ι := { app := fun j => CostructuredArrow.homMk (c.ι.app j) rfl }

@[simps]
def Cocone.toStructuredArrow (F : J ⥤ C) : Cocone F ⥤ StructuredArrow F (const J) where
  obj c := StructuredArrow.mk c.ι
  map f := StructuredArrow.homMk f.hom

@[simps]
def Cocone.fromStructuredArrow (F : J ⥤ C) : StructuredArrow F (const J) ⥤ Cocone F where
  obj c := ⟨c.right, c.hom⟩
  map f :=
    { hom := f.right
      w := fun j => by
        convert (congr_fun (congr_arg NatTrans.app f.w) j).symm
        dsimp
        simp }

@[simps]
def Cocone.equivStructuredArrow (F : J ⥤ C) : Cocone F ≌ StructuredArrow F (const J) where
  functor := Cocone.toStructuredArrow F
  inverse := Cocone.fromStructuredArrow F
  unitIso := NatIso.ofComponents Cocones.eta
  counitIso := NatIso.ofComponents fun _ => (StructuredArrow.eta _).symm

def Cocone.isColimitEquivIsInitial {F : J ⥤ C} (c : Cocone F) : IsColimit c ≃ IsInitial c :=
  IsColimit.isoUniqueCoconeMorphism.toEquiv.trans
    { toFun := fun _ => IsInitial.ofUnique _
      invFun := fun h s => ⟨⟨IsInitial.to h s⟩, fun a => IsInitial.hom_ext h a _⟩
      left_inv := by aesop_cat
      right_inv := by aesop_cat }

theorem hasColimit_iff_hasInitial_cocone (F : J ⥤ C) : HasColimit F ↔ HasInitial (Cocone F) :=
  ⟨fun _ => (Cocone.isColimitEquivIsInitial _ (colimit.isColimit F)).hasInitial, fun h =>
    haveI : HasInitial (Cocone F) := h
    ⟨⟨⟨⊥_ _, (Cocone.isColimitEquivIsInitial _).symm initialIsInitial⟩⟩⟩⟩

theorem hasColimitsOfShape_iff_isRightAdjoint_const :
    HasColimitsOfShape J C ↔ IsRightAdjoint (const J : C ⥤ _) :=
  calc
    HasColimitsOfShape J C ↔ ∀ F : J ⥤ C, HasColimit F :=
      ⟨fun h => h.has_colimit, fun h => HasColimitsOfShape.mk⟩
    _ ↔ ∀ F : J ⥤ C, HasInitial (Cocone F) := forall_congr' hasColimit_iff_hasInitial_cocone
    _ ↔ ∀ F : J ⥤ C, HasInitial (StructuredArrow F (const J)) :=
      (forall_congr' fun F => (Cocone.equivStructuredArrow F).hasInitial_iff)
    _ ↔ (IsRightAdjoint (const J : C ⥤ _)) :=
      isRightAdjoint_iff_hasInitial_structuredArrow.symm

theorem IsColimit.descCoconeMorphism_eq_isInitial_to {F : J ⥤ C} {c : Cocone F} (hc : IsColimit c)
    (s : Cocone F) :
    hc.descCoconeMorphism s = IsInitial.to (Cocone.isColimitEquivIsInitial _ hc) _ :=
  rfl

theorem IsInitial.to_eq_descCoconeMorphism {F : J ⥤ C} {c : Cocone F} (hc : IsInitial c)
    (s : Cocone F) :
    IsInitial.to hc s = ((Cocone.isColimitEquivIsInitial _).symm hc).descCoconeMorphism s :=
  (IsColimit.descCoconeMorphism_eq_isInitial_to (c.isColimitEquivIsInitial.symm hc) s).symm

noncomputable def IsColimit.ofPreservesCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [PreservesColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit c) :
    IsColimit (G.obj c) :=
  (Cocone.isColimitEquivIsInitial _).symm <| (Cocone.isColimitEquivIsInitial _ hc).isInitialObj _ _

noncomputable def IsColimit.ofReflectsCoconeInitial {F : J ⥤ C} {F' : K ⥤ D}
    (G : Cocone F ⥤ Cocone F')
    [ReflectsColimit (Functor.empty.{0} _) G] {c : Cocone F} (hc : IsColimit (G.obj c)) :
    IsColimit c :=
  (Cocone.isColimitEquivIsInitial _).symm <|
    (Cocone.isColimitEquivIsInitial _ hc).isInitialOfObj _ _

end CategoryTheory.Limits
