/-
Extracted from Geometry/RingedSpace/SheafedSpace.lean
Genuine: 13 | Conflates: 0 | Dissolved: 0 | Infrastructure: 23
-/
import Origin.Core
import Mathlib.Geometry.RingedSpace.PresheafedSpace.HasColimits
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.Topology.Sheaves.Functors

noncomputable section

/-!
# Sheafed spaces

Introduces the category of topological spaces equipped with a sheaf (taking values in an
arbitrary target category `C`.)

We further describe how to apply functors and natural transformations to the values of the
presheaves.
-/

open CategoryTheory TopCat TopologicalSpace Opposite CategoryTheory.Limits CategoryTheory.Category

  CategoryTheory.Functor Topology

universe u v

variable (C : Type u) [Category.{v} C]

namespace AlgebraicGeometry

structure SheafedSpace extends PresheafedSpace C where
  /-- A sheafed space is presheafed space which happens to be sheaf. -/
  IsSheaf : presheaf.IsSheaf

variable {C}

namespace SheafedSpace

instance coeCarrier : CoeOut (SheafedSpace C) TopCat where coe X := X.carrier

instance coeSort : CoeSort (SheafedSpace C) Type* where
  coe X := X.1

def sheaf (X : SheafedSpace C) : Sheaf C (X : TopCat) :=
  ⟨X.presheaf, X.IsSheaf⟩

instance (X : SheafedSpace C) : TopologicalSpace X :=
  X.carrier.str

def unit (X : TopCat) : SheafedSpace (Discrete Unit) :=
  { @PresheafedSpace.const (Discrete Unit) _ X ⟨⟨⟩⟩ with IsSheaf := Presheaf.isSheaf_unit _ }

instance : Inhabited (SheafedSpace (Discrete Unit)) :=
  ⟨unit (TopCat.of PEmpty)⟩

instance : Category (SheafedSpace C) :=
  show Category (InducedCategory (PresheafedSpace C) SheafedSpace.toPresheafedSpace) by
    infer_instance

@[ext (iff := false)]
theorem ext {X Y : SheafedSpace C} (α β : X ⟶ Y) (w : α.base = β.base)
    (h : α.c ≫ whiskerRight (eqToHom (by rw [w])) _ = β.c) : α = β :=
  PresheafedSpace.ext α β w h

@[simps]
def isoMk {X Y : SheafedSpace C} (e : X.toPresheafedSpace ≅ Y.toPresheafedSpace) : X ≅ Y where
  hom := e.hom
  inv := e.inv
  hom_inv_id := e.hom_inv_id
  inv_hom_id := e.inv_hom_id

@[simps! obj map]
def forgetToPresheafedSpace : SheafedSpace C ⥤ PresheafedSpace C :=
  inducedFunctor _

instance forgetToPresheafedSpace_full : (forgetToPresheafedSpace (C := C)).Full where
  map_surjective f := ⟨f, rfl⟩

instance forgetToPresheafedSpace_faithful : (forgetToPresheafedSpace (C := C)).Faithful where

instance is_presheafedSpace_iso {X Y : SheafedSpace C} (f : X ⟶ Y) [IsIso f] :
    @IsIso (PresheafedSpace C) _ _ _ f :=
  SheafedSpace.forgetToPresheafedSpace.map_isIso f

section

attribute [local simp] id comp

@[simp]
theorem id_base (X : SheafedSpace C) : (𝟙 X : X ⟶ X).base = 𝟙 (X : TopCat) :=
  rfl

@[simp]
theorem id_c_app (X : SheafedSpace C) (U) :
    (𝟙 X : X ⟶ X).c.app U = 𝟙 _ := rfl

@[simp]
theorem comp_base {X Y Z : SheafedSpace C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simp]
theorem comp_c_app {X Y Z : SheafedSpace C} (α : X ⟶ Y) (β : Y ⟶ Z) (U) :
    (α ≫ β).c.app U = β.c.app U ≫ α.c.app (op ((Opens.map β.base).obj (unop U))) :=
  rfl

theorem congr_app {X Y : SheafedSpace C} {α β : X ⟶ Y} (h : α = β) (U) :
    α.c.app U = β.c.app U ≫ X.presheaf.map (eqToHom (by subst h; rfl)) :=
  PresheafedSpace.congr_app h U

variable (C)

def forget : SheafedSpace C ⥤ TopCat where
  obj X := (X : TopCat)
  map {_ _} f := f.base

end

open TopCat.Presheaf

def restrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)} (h : IsOpenEmbedding f) :
    SheafedSpace C :=
  { X.toPresheafedSpace.restrict h with IsSheaf := isSheaf_of_isOpenEmbedding h X.IsSheaf }

@[simps!]
def ofRestrict {U : TopCat} (X : SheafedSpace C) {f : U ⟶ (X : TopCat)}
    (h : IsOpenEmbedding f) : X.restrict h ⟶ X := X.toPresheafedSpace.ofRestrict h

@[simps! hom inv]
def restrictTopIso (X : SheafedSpace C) : X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoMk (X.toPresheafedSpace.restrictTopIso)

def Γ : (SheafedSpace C)ᵒᵖ ⥤ C :=
  forgetToPresheafedSpace.op ⋙ PresheafedSpace.Γ

@[simp]
theorem Γ_obj (X : (SheafedSpace C)ᵒᵖ) : Γ.obj X = (unop X).presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : (SheafedSpace C)ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

noncomputable instance [HasLimits C] :
    CreatesColimits (forgetToPresheafedSpace : SheafedSpace C ⥤ _) :=
  ⟨fun {_ _} =>
    ⟨fun {K} =>
      createsColimitOfFullyFaithfulOfIso
        ⟨(PresheafedSpace.colimitCocone (K ⋙ forgetToPresheafedSpace)).pt,
          limit_isSheaf _ fun j => Sheaf.pushforward_sheaf_of_sheaf _ (K.obj (unop j)).2⟩
        (colimit.isoColimitCocone ⟨_, PresheafedSpace.colimitCoconeIsColimit _⟩).symm⟩⟩

instance [HasLimits C] : HasColimits.{v} (SheafedSpace C) :=
  hasColimits_of_hasColimits_createsColimits forgetToPresheafedSpace

noncomputable instance [HasLimits C] : PreservesColimits (forget.{_, _, v} C) :=
  Limits.comp_preservesColimits forgetToPresheafedSpace (PresheafedSpace.forget C)

section ConcreteCategory

variable [ConcreteCategory.{v} C] [HasColimits C] [HasLimits C]

variable  [PreservesLimits (CategoryTheory.forget C)]

variable [PreservesFilteredColimits (CategoryTheory.forget C)]

variable [(CategoryTheory.forget C).ReflectsIsomorphisms]

attribute [local instance] ConcreteCategory.instFunLike in
lemma hom_stalk_ext {X Y : SheafedSpace C} (f g : X ⟶ Y) (h : f.base = g.base)
    (h' : ∀ x, f.stalkMap x = (Y.presheaf.stalkCongr (h ▸ rfl)).hom ≫ g.stalkMap x) :
    f = g := by
  obtain ⟨f, fc⟩ := f
  obtain ⟨g, gc⟩ := g
  obtain rfl : f = g := h
  congr
  ext U s
  refine section_ext X.sheaf _ _ _ fun x hx ↦
    show X.presheaf.germ _ x _ _ = X.presheaf.germ _ x _ _ from ?_
  erw [← PresheafedSpace.stalkMap_germ_apply ⟨f, fc⟩, ← PresheafedSpace.stalkMap_germ_apply ⟨f, gc⟩]
  simp [h']

lemma mono_of_base_injective_of_stalk_epi {X Y : SheafedSpace C} (f : X ⟶ Y)
    (h₁ : Function.Injective f.base)
    (h₂ : ∀ x, Epi (f.stalkMap x)) : Mono f := by
  constructor
  intro Z ⟨g, gc⟩ ⟨h, hc⟩ e
  obtain rfl : g = h := ConcreteCategory.hom_ext _ _ fun x ↦ h₁ congr(($e).base x)
  refine SheafedSpace.hom_stalk_ext ⟨g, gc⟩ ⟨g, hc⟩ rfl fun x ↦ ?_
  rw [← cancel_epi (f.stalkMap (g x)), stalkCongr_hom, stalkSpecializes_refl, Category.id_comp,
    ← PresheafedSpace.stalkMap.comp ⟨g, gc⟩ f, ← PresheafedSpace.stalkMap.comp ⟨g, hc⟩ f]
  congr 1

end ConcreteCategory

end SheafedSpace

end AlgebraicGeometry
