/-
Extracted from CategoryTheory/Limits/Preserves/Shapes/Biproducts.lean
Genuine: 38 | Conflates: 0 | Dissolved: 0 | Infrastructure: 12
-/
import Origin.Core
import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

noncomputable section

/-!
# Preservation of biproducts

We define the image of a (binary) bicone under a functor that preserves zero morphisms and define
classes `PreservesBiproduct` and `PreservesBinaryBiproduct`. We then

* show that a functor that preserves biproducts of a two-element type preserves binary biproducts,
* construct the comparison morphisms between the image of a biproduct and the biproduct of the
  images and show that the biproduct is preserved if one of them is an isomorphism,
* give the canonical isomorphism between the image of a biproduct and the biproduct of the images
  in case that the biproduct is preserved.

-/

universe w₁ w₂ v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

section HasZeroMorphisms

variable [HasZeroMorphisms C] [HasZeroMorphisms D]

namespace Functor

section Map

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁}

@[simps]
def mapBicone {f : J → C} (b : Bicone f) : Bicone (F.obj ∘ f) where
  pt := F.obj b.pt
  π j := F.map (b.π j)
  ι j := F.map (b.ι j)
  ι_π j j' := by
    rw [← F.map_comp]
    split_ifs with h
    · subst h
      simp only [bicone_ι_π_self, CategoryTheory.Functor.map_id, eqToHom_refl]; dsimp
    · rw [bicone_ι_π_ne _ h, F.map_zero]

end Bicone

@[simps!]
def mapBinaryBicone {X Y : C} (b : BinaryBicone X Y) : BinaryBicone (F.obj X) (F.obj Y) :=
  (BinaryBicones.functoriality _ _ F).obj b

end Map

end Functor

open CategoryTheory.Functor

namespace Limits

section Bicone

variable {J : Type w₁} {K : Type w₂}

class PreservesBiproduct (f : J → C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : Bicone f}, b.IsBilimit → Nonempty (F.mapBicone b).IsBilimit

attribute [inherit_doc PreservesBiproduct] PreservesBiproduct.preserves

def isBilimitOfPreserves {f : J → C} (F : C ⥤ D) [PreservesZeroMorphisms F] [PreservesBiproduct f F]
    {b : Bicone f} (hb : b.IsBilimit) : (F.mapBicone b).IsBilimit :=
  (PreservesBiproduct.preserves hb).some

variable (J)

class PreservesBiproductsOfShape (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {f : J → C}, PreservesBiproduct f F

attribute [inherit_doc PreservesBiproductsOfShape] PreservesBiproductsOfShape.preserves

attribute [instance 100] PreservesBiproductsOfShape.preserves

end Bicone

class PreservesFiniteBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type} [Fintype J], PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesFiniteBiproducts] PreservesFiniteBiproducts.preserves

attribute [instance 100] PreservesFiniteBiproducts.preserves

class PreservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {J : Type w₁}, PreservesBiproductsOfShape J F

attribute [inherit_doc PreservesBiproducts] PreservesBiproducts.preserves

attribute [instance 100] PreservesBiproducts.preserves

lemma preservesBiproducts_shrink (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproducts.{max w₁ w₂} F] : PreservesBiproducts.{w₁} F :=
  ⟨fun {_} =>
    ⟨fun {_} =>
      ⟨fun {b} ib =>
        ⟨((F.mapBicone b).whiskerIsBilimitIff _).toFun
          (isBilimitOfPreserves F ((b.whiskerIsBilimitIff Equiv.ulift.{w₂}).invFun ib))⟩⟩⟩⟩

instance (priority := 100) preservesFiniteBiproductsOfPreservesBiproducts (F : C ⥤ D)
    [PreservesZeroMorphisms F] [PreservesBiproducts.{w₁} F] : PreservesFiniteBiproducts F where
  preserves {J} _ := by letI := preservesBiproducts_shrink.{0} F; infer_instance

class PreservesBinaryBiproduct (X Y : C) (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {b : BinaryBicone X Y}, b.IsBilimit → Nonempty ((F.mapBinaryBicone b).IsBilimit)

attribute [inherit_doc PreservesBinaryBiproduct] PreservesBinaryBiproduct.preserves

def isBinaryBilimitOfPreserves {X Y : C} (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBinaryBiproduct X Y F] {b : BinaryBicone X Y} (hb : b.IsBilimit) :
    (F.mapBinaryBicone b).IsBilimit :=
  (PreservesBinaryBiproduct.preserves hb).some

class PreservesBinaryBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F] : Prop where
  preserves : ∀ {X Y : C}, PreservesBinaryBiproduct X Y F := by infer_instance

attribute [inherit_doc PreservesBinaryBiproducts] PreservesBinaryBiproducts.preserves

lemma preservesBinaryBiproduct_of_preservesBiproduct (F : C ⥤ D)
    [PreservesZeroMorphisms F] (X Y : C) [PreservesBiproduct (pairFunction X Y) F] :
    PreservesBinaryBiproduct X Y F where
  preserves {b} hb := ⟨{
      isLimit :=
        IsLimit.ofIsoLimit
            ((IsLimit.postcomposeHomEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isLimit) <|
          Cones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp
      isColimit :=
        IsColimit.ofIsoColimit
            ((IsColimit.precomposeInvEquiv (diagramIsoPair _) _).symm
              (isBilimitOfPreserves F (b.toBiconeIsBilimit.symm hb)).isColimit) <|
          Cocones.ext (Iso.refl _) fun j => by
            rcases j with ⟨⟨⟩⟩ <;> simp }⟩

lemma preservesBinaryBiproducts_of_preservesBiproducts (F : C ⥤ D) [PreservesZeroMorphisms F]
    [PreservesBiproductsOfShape WalkingPair F] : PreservesBinaryBiproducts F where
  preserves {X} Y := preservesBinaryBiproduct_of_preservesBiproduct F X Y

attribute [instance 100] PreservesBinaryBiproducts.preserves

end Limits

open CategoryTheory.Limits

namespace Functor

section Bicone

variable {J : Type w₁} (F : C ⥤ D) (f : J → C) [HasBiproduct f]

section

variable [HasBiproduct (F.obj ∘ f)]

def biproductComparison : F.obj (⨁ f) ⟶ ⨁ F.obj ∘ f :=
  biproduct.lift fun j => F.map (biproduct.π f j)

@[reassoc (attr := simp)]
theorem biproductComparison_π (j : J) :
    biproductComparison F f ≫ biproduct.π _ j = F.map (biproduct.π f j) :=
  biproduct.lift_π _ _

def biproductComparison' : ⨁ F.obj ∘ f ⟶ F.obj (⨁ f) :=
  biproduct.desc fun j => F.map (biproduct.ι f j)

@[reassoc (attr := simp)]
theorem ι_biproductComparison' (j : J) :
    biproduct.ι _ j ≫ biproductComparison' F f = F.map (biproduct.ι f j) :=
  biproduct.ι_desc _ _

variable [PreservesZeroMorphisms F]

@[reassoc (attr := simp)]
theorem biproductComparison'_comp_biproductComparison :
    biproductComparison' F f ≫ biproductComparison F f = 𝟙 (⨁ F.obj ∘ f) := by
  classical
    ext
    simp [biproduct.ι_π, ← Functor.map_comp, eqToHom_map]

@[simps]
def splitEpiBiproductComparison : SplitEpi (biproductComparison F f) where
  section_ := biproductComparison' F f
  id := by aesop

instance : IsSplitEpi (biproductComparison F f) :=
  IsSplitEpi.mk' (splitEpiBiproductComparison F f)

@[simps]
def splitMonoBiproductComparison' : SplitMono (biproductComparison' F f) where
  retraction := biproductComparison F f
  id := by aesop

instance : IsSplitMono (biproductComparison' F f) :=
  IsSplitMono.mk' (splitMonoBiproductComparison' F f)

end

variable [PreservesZeroMorphisms F] [PreservesBiproduct f F]

instance hasBiproduct_of_preserves : HasBiproduct (F.obj ∘ f) :=
  HasBiproduct.mk
    { bicone := F.mapBicone (biproduct.bicone f)
      isBilimit := isBilimitOfPreserves _ (biproduct.isBilimit _) }

@[simp]
def mapBiproduct : F.obj (⨁ f) ≅ ⨁ F.obj ∘ f :=
  biproduct.uniqueUpToIso _ (isBilimitOfPreserves _ (biproduct.isBilimit _))

theorem mapBiproduct_hom :
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (mapBiproduct F f).hom = biproduct.lift fun j => F.map (biproduct.π f j) := rfl

theorem mapBiproduct_inv :
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (mapBiproduct F f).inv = biproduct.desc fun j => F.map (biproduct.ι f j) := rfl

end Bicone

variable (F : C ⥤ D) (X Y : C) [HasBinaryBiproduct X Y]

section

variable [HasBinaryBiproduct (F.obj X) (F.obj Y)]

def biprodComparison : F.obj (X ⊞ Y) ⟶ F.obj X ⊞ F.obj Y :=
  biprod.lift (F.map biprod.fst) (F.map biprod.snd)

@[reassoc (attr := simp)]
theorem biprodComparison_fst : biprodComparison F X Y ≫ biprod.fst = F.map biprod.fst :=
  biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem biprodComparison_snd : biprodComparison F X Y ≫ biprod.snd = F.map biprod.snd :=
  biprod.lift_snd _ _

def biprodComparison' : F.obj X ⊞ F.obj Y ⟶ F.obj (X ⊞ Y) :=
  biprod.desc (F.map biprod.inl) (F.map biprod.inr)

@[reassoc (attr := simp)]
theorem inl_biprodComparison' : biprod.inl ≫ biprodComparison' F X Y = F.map biprod.inl :=
  biprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_biprodComparison' : biprod.inr ≫ biprodComparison' F X Y = F.map biprod.inr :=
  biprod.inr_desc _ _

variable [PreservesZeroMorphisms F]

@[reassoc (attr := simp)]
theorem biprodComparison'_comp_biprodComparison :
    biprodComparison' F X Y ≫ biprodComparison F X Y = 𝟙 (F.obj X ⊞ F.obj Y) := by
  ext <;> simp [← Functor.map_comp]

@[simps]
def splitEpiBiprodComparison : SplitEpi (biprodComparison F X Y) where
  section_ := biprodComparison' F X Y
  id := by aesop

instance : IsSplitEpi (biprodComparison F X Y) :=
  IsSplitEpi.mk' (splitEpiBiprodComparison F X Y)

@[simps]
def splitMonoBiprodComparison' : SplitMono (biprodComparison' F X Y) where
  retraction := biprodComparison F X Y
  id := by aesop

instance : IsSplitMono (biprodComparison' F X Y) :=
  IsSplitMono.mk' (splitMonoBiprodComparison' F X Y)

end

variable [PreservesZeroMorphisms F] [PreservesBinaryBiproduct X Y F]

instance hasBinaryBiproduct_of_preserves : HasBinaryBiproduct (F.obj X) (F.obj Y) :=
  HasBinaryBiproduct.mk
    { bicone := F.mapBinaryBicone (BinaryBiproduct.bicone X Y)
      isBilimit := isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _) }

@[simp]
def mapBiprod : F.obj (X ⊞ Y) ≅ F.obj X ⊞ F.obj Y :=
  biprod.uniqueUpToIso _ _ (isBinaryBilimitOfPreserves F (BinaryBiproduct.isBilimit _ _))

end Functor

namespace Limits

variable (F : C ⥤ D) [PreservesZeroMorphisms F]

section Bicone

variable {J : Type w₁} (f : J → C) [HasBiproduct f] [PreservesBiproduct f F] {W : C}

theorem biproduct.map_lift_mapBiprod (g : ∀ j, W ⟶ f j) :
    -- Porting note: twice we need haveI to tell Lean about hasBiproduct_of_preserves F f
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    F.map (biproduct.lift g) ≫ (F.mapBiproduct f).hom = biproduct.lift fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
  simp only [mapBiproduct_hom, Category.assoc, biproduct.lift_π, ← F.map_comp]

theorem biproduct.mapBiproduct_inv_map_desc (g : ∀ j, f j ⟶ W) :
    -- Porting note: twice we need haveI to tell Lean about hasBiproduct_of_preserves F f
    haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
    (F.mapBiproduct f).inv ≫ F.map (biproduct.desc g) = biproduct.desc fun j => F.map (g j) := by
  ext j
  dsimp only [Function.comp_def]
  haveI : HasBiproduct fun j => F.obj (f j) := hasBiproduct_of_preserves F f
  simp only [mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc ,← F.map_comp]

theorem biproduct.mapBiproduct_hom_desc (g : ∀ j, f j ⟶ W) :
    ((F.mapBiproduct f).hom ≫ biproduct.desc fun j => F.map (g j)) = F.map (biproduct.desc g) := by
  rw [← biproduct.mapBiproduct_inv_map_desc, Iso.hom_inv_id_assoc]

end Bicone

section BinaryBicone

variable (X Y : C) [HasBinaryBiproduct X Y] [PreservesBinaryBiproduct X Y F] {W : C}

theorem biprod.map_lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    F.map (biprod.lift f g) ≫ (F.mapBiprod X Y).hom = biprod.lift (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

theorem biprod.lift_mapBiprod (f : W ⟶ X) (g : W ⟶ Y) :
    biprod.lift (F.map f) (F.map g) ≫ (F.mapBiprod X Y).inv = F.map (biprod.lift f g) := by
  rw [← biprod.map_lift_mapBiprod, Category.assoc, Iso.hom_inv_id, Category.comp_id]

theorem biprod.mapBiprod_inv_map_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).inv ≫ F.map (biprod.desc f g) = biprod.desc (F.map f) (F.map g) := by
  ext <;> simp [mapBiprod, ← F.map_comp]

theorem biprod.mapBiprod_hom_desc (f : X ⟶ W) (g : Y ⟶ W) :
    (F.mapBiprod X Y).hom ≫ biprod.desc (F.map f) (F.map g) = F.map (biprod.desc f g) := by
  rw [← biprod.mapBiprod_inv_map_desc, Iso.hom_inv_id_assoc]

end BinaryBicone

end Limits

end HasZeroMorphisms

end CategoryTheory
