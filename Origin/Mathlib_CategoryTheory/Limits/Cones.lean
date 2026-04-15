/-
Extracted from CategoryTheory/Limits/Cones.lean
Genuine: 94 | Conflates: 0 | Dissolved: 0 | Infrastructure: 14
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.Const
import Mathlib.CategoryTheory.DiscreteCategory
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Functor.ReflectsIso

/-!
# Cones and cocones

We define `Cone F`, a cone over a functor `F`,
and `F.cones : Cᵒᵖ ⥤ Type`, the functor associating to `X` the cones over `F` with cone point `X`.

A cone `c` is defined by specifying its cone point `c.pt` and a natural transformation `c.π`
from the constant `c.pt` valued functor to `F`.

We provide `c.w f : c.π.app j ≫ F.map f = c.π.app j'` for any `f : j ⟶ j'`
as a wrapper for `c.π.naturality f` avoiding unneeded identity morphisms.

We define `c.extend f`, where `c : cone F` and `f : Y ⟶ c.pt` for some other `Y`,
which replaces the cone point by `Y` and inserts `f` into each of the components of the cone.
Similarly we have `c.whisker F` producing a `Cone (E ⋙ F)`

We define morphisms of cones, and the category of cones.

We define `Cone.postcompose α : cone F ⥤ cone G` for `α` a natural transformation `F ⟶ G`.

And, of course, we dualise all this to cocones as well.

For more results about the category of cones, see `cone_category.lean`.
-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

open CategoryTheory

variable {J : Type u₁} [Category.{v₁} J]

variable {K : Type u₂} [Category.{v₂} K]

variable {C : Type u₃} [Category.{v₃} C]

variable {D : Type u₄} [Category.{v₄} D]

open CategoryTheory

open CategoryTheory.Category

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory

namespace Functor

variable (F : J ⥤ C)

@[simps!]
def cones : Cᵒᵖ ⥤ Type max u₁ v₃ :=
  (const J).op ⋙ yoneda.obj F

@[simps!]
def cocones : C ⥤ Type max u₁ v₃ :=
  const J ⋙ coyoneda.obj (op F)

end Functor

section

variable (J C)

@[simps!]
def cones : (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type max u₁ v₃ where
  obj := Functor.cones
  map f := whiskerLeft (const J).op (yoneda.map f)

@[simps!]
def cocones : (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type max u₁ v₃ where
  obj F := Functor.cocones (unop F)
  map f := whiskerLeft (const J) (coyoneda.map f)

end

namespace Limits

section

structure Cone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from the constant functor at `X` to `F` -/
  π : (const J).obj pt ⟶ F

instance inhabitedCone (F : Discrete PUnit ⥤ C) : Inhabited (Cone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      π := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                aesop_cat
           }
  }⟩

@[reassoc (attr := simp)]
theorem Cone.w {F : J ⥤ C} (c : Cone F) {j j' : J} (f : j ⟶ j') :
    c.π.app j ≫ F.map f = c.π.app j' := by
  rw [← c.π.naturality f]
  apply id_comp

structure Cocone (F : J ⥤ C) where
  /-- An object of `C` -/
  pt : C
  /-- A natural transformation from `F` to the constant functor at `pt` -/
  ι : F ⟶ (const J).obj pt

instance inhabitedCocone (F : Discrete PUnit ⥤ C) : Inhabited (Cocone F) :=
  ⟨{  pt := F.obj ⟨⟨⟩⟩
      ι := { app := fun ⟨⟨⟩⟩ => 𝟙 _
             naturality := by
              intro X Y f
              match X, Y, f with
              | .mk A, .mk B, .up g =>
                aesop_cat
           }
  }⟩

@[reassoc]
theorem Cocone.w {F : J ⥤ C} (c : Cocone F) {j j' : J} (f : j ⟶ j') :
    F.map f ≫ c.ι.app j' = c.ι.app j := by
  rw [c.ι.naturality f]
  apply comp_id

attribute [simp 1001] Cocone.w_assoc

end

variable {F : J ⥤ C}

namespace Cone

@[simps!]
def equiv (F : J ⥤ C) : Cone F ≅ ΣX, F.cones.obj X where
  hom c := ⟨op c.pt, c.π⟩
  inv c :=
    { pt := c.1.unop
      π := c.2 }
  hom_inv_id := by
    funext X
    cases X
    rfl
  inv_hom_id := by
    funext X
    cases X
    rfl

@[simps]
def extensions (c : Cone F) : yoneda.obj c.pt ⋙ uliftFunctor.{u₁} ⟶ F.cones where
  app _ f := (const J).map f.down ≫ c.π

@[simps]
def extend (c : Cone F) {X : C} (f : X ⟶ c.pt) : Cone F :=
  { pt := X
    π := c.extensions.app (op X) ⟨f⟩ }

@[simps]
def whisker (E : K ⥤ J) (c : Cone F) : Cone (E ⋙ F) where
  pt := c.pt
  π := whiskerLeft E c.π

end Cone

namespace Cocone

def equiv (F : J ⥤ C) : Cocone F ≅ ΣX, F.cocones.obj X where
  hom c := ⟨c.pt, c.ι⟩
  inv c :=
    { pt := c.1
      ι := c.2 }
  hom_inv_id := by
    funext X
    cases X
    rfl
  inv_hom_id := by
    funext X
    cases X
    rfl

@[simps]
def extensions (c : Cocone F) : coyoneda.obj (op c.pt) ⋙ uliftFunctor.{u₁} ⟶ F.cocones where
  app _ f := c.ι ≫ (const J).map f.down

@[simps]
def extend (c : Cocone F) {Y : C} (f : c.pt ⟶ Y) : Cocone F where
  pt := Y
  ι := c.extensions.app Y ⟨f⟩

@[simps]
def whisker (E : K ⥤ J) (c : Cocone F) : Cocone (E ⋙ F) where
  pt := c.pt
  ι := whiskerLeft E c.ι

end Cocone

structure ConeMorphism (A B : Cone F) where
  /-- A morphism between the two vertex objects of the cones -/
  hom : A.pt ⟶ B.pt
  /-- The triangle consisting of the two natural transformations and `hom` commutes -/
  w : ∀ j : J, hom ≫ B.π.app j = A.π.app j := by aesop_cat

attribute [reassoc (attr := simp)] ConeMorphism.w

instance inhabitedConeMorphism (A : Cone F) : Inhabited (ConeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

@[simps]
instance Cone.category : Category (Cone F) where
  Hom A B := ConeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

@[ext]
theorem ConeMorphism.ext {c c' : Cone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Cones

@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Cone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.π.app j = φ.hom ≫ c'.π.app j := by aesop_cat) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.inv_comp_eq.mpr (w j) }

@[simps!]
def eta (c : Cone F) : c ≅ ⟨c.pt, c.π⟩ :=
  Cones.ext (Iso.refl _)

theorem cone_iso_of_hom_iso {K : J ⥤ C} {c d : Cone K} (f : c ⟶ d) [i : IsIso f.hom] : IsIso f :=
  ⟨⟨{   hom := inv f.hom
        w := fun j => (asIso f.hom).inv_comp_eq.2 (f.w j).symm }, by aesop_cat⟩⟩

@[simps]
def extend (s : Cone F) {X : C} (f : X ⟶ s.pt) : s.extend f ⟶ s where
  hom := f

@[simps!]
def extendId (s : Cone F) : s.extend (𝟙 s.pt) ≅ s :=
  Cones.ext (Iso.refl _)

@[simps!]
def extendComp (s : Cone F) {X Y : C} (f : X ⟶ Y) (g : Y ⟶ s.pt) :
    s.extend (f ≫ g) ≅ (s.extend g).extend f :=
  Cones.ext (Iso.refl _)

@[simps]
def extendIso (s : Cone F) {X : C} (f : X ≅ s.pt) : s.extend f.hom ≅ s where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

instance {s : Cone F} {X : C} (f : X ⟶ s.pt) [IsIso f] : IsIso (Cones.extend s f) :=
  ⟨(extendIso s (asIso f)).inv, by aesop_cat⟩

@[simps]
def postcompose {G : J ⥤ C} (α : F ⟶ G) : Cone F ⥤ Cone G where
  obj c :=
    { pt := c.pt
      π := c.π ≫ α }
  map f := { hom := f.hom }

@[simps!]
def postcomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    postcompose (α ≫ β) ≅ postcompose α ⋙ postcompose β :=
  NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

@[simps!]
def postcomposeId : postcompose (𝟙 F) ≅ 𝟭 (Cone F) :=
  NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

@[simps]
def postcomposeEquivalence {G : J ⥤ C} (α : F ≅ G) : Cone F ≌ Cone G where
  functor := postcompose α.hom
  inverse := postcompose α.inv
  unitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)

@[simps]
def whiskering (E : K ⥤ J) : Cone F ⥤ Cone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

@[simps]
def whiskeringEquivalence (e : K ≌ J) : Cone F ≌ Cone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse := whiskering e.inverse ⋙ postcompose (e.invFunIdAssoc F).hom
  unitIso := NatIso.ofComponents fun s => Cones.ext (Iso.refl _)
  counitIso :=
    NatIso.ofComponents
      fun s =>
        Cones.ext (Iso.refl _)
          (by
            intro k
            simpa [e.counit_app_functor] using s.w (e.unitInv.app k))

@[simps! functor inverse unitIso counitIso]
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cone F ≌ Cone G :=
  (whiskeringEquivalence e).trans (postcomposeEquivalence α)

section

variable (F)

@[simps]
def forget : Cone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

@[simps]
def functoriality : Cone F ⥤ Cone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      π :=
        { app := fun j => G.map (A.π.app j)
          naturality := by intros; erw [← G.map_comp]; aesop_cat } }
  map f :=
    { hom := G.map f.hom
      w := fun j => by simp [-ConeMorphism.w, ← f.w j] }

instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by aesop_cat⟩

instance functoriality_faithful [G.Faithful] : (Cones.functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    ConeMorphism.ext f g <| G.map_injective <| congr_arg ConeMorphism.hom h

@[simps]
def functorialityEquivalence (e : C ≌ D) : Cone F ≌ Cone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (postcomposeEquivalence f).functor
    unitIso := NatIso.ofComponents fun c => Cones.ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => Cones.ext (e.counitIso.app _) }

instance reflects_cone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (Cones.functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  haveI : IsIso (F.map f.hom) :=
    (Cones.forget (K ⋙ F)).map_isIso ((Cones.functoriality K F).map f)
  haveI := ReflectsIsomorphisms.reflects F f.hom
  apply cone_iso_of_hom_iso

end

end Cones

structure CoconeMorphism (A B : Cocone F) where
  /-- A morphism between the (co)vertex objects in `C` -/
  hom : A.pt ⟶ B.pt
  /-- The triangle made from the two natural transformations and `hom` commutes -/
  w : ∀ j : J, A.ι.app j ≫ hom = B.ι.app j := by aesop_cat

instance inhabitedCoconeMorphism (A : Cocone F) : Inhabited (CoconeMorphism A A) :=
  ⟨{ hom := 𝟙 _ }⟩

attribute [reassoc (attr := simp)] CoconeMorphism.w

@[simps]
instance Cocone.category : Category (Cocone F) where
  Hom A B := CoconeMorphism A B
  comp f g := { hom := f.hom ≫ g.hom }
  id B := { hom := 𝟙 B.pt }

@[ext]
theorem CoconeMorphism.ext {c c' : Cocone F} (f g : c ⟶ c') (w : f.hom = g.hom) : f = g := by
  cases f
  cases g
  congr

namespace Cocones

@[aesop apply safe (rule_sets := [CategoryTheory]), simps]
def ext {c c' : Cocone F} (φ : c.pt ≅ c'.pt)
    (w : ∀ j, c.ι.app j ≫ φ.hom = c'.ι.app j := by aesop_cat) : c ≅ c' where
  hom := { hom := φ.hom }
  inv :=
    { hom := φ.inv
      w := fun j => φ.comp_inv_eq.mpr (w j).symm }

@[simps!]
def eta (c : Cocone F) : c ≅ ⟨c.pt, c.ι⟩ :=
  Cocones.ext (Iso.refl _)

theorem cocone_iso_of_hom_iso {K : J ⥤ C} {c d : Cocone K} (f : c ⟶ d) [i : IsIso f.hom] :
    IsIso f :=
  ⟨⟨{ hom := inv f.hom
      w := fun j => (asIso f.hom).comp_inv_eq.2 (f.w j).symm }, by aesop_cat⟩⟩

@[simps]
def extend (s : Cocone F) {X : C} (f : s.pt ⟶ X) : s ⟶ s.extend f where
  hom := f

@[simps!]
def extendId (s : Cocone F) : s ≅ s.extend (𝟙 s.pt) :=
  Cocones.ext (Iso.refl _)

@[simps!]
def extendComp (s : Cocone F) {X Y : C} (f : s.pt ⟶ X) (g : X ⟶ Y) :
    s.extend (f ≫ g) ≅ (s.extend f).extend g :=
  Cocones.ext (Iso.refl _)

@[simps]
def extendIso (s : Cocone F) {X : C} (f : s.pt ≅ X) : s ≅ s.extend f.hom where
  hom := { hom := f.hom }
  inv := { hom := f.inv }

instance {s : Cocone F} {X : C} (f : s.pt ⟶ X) [IsIso f] : IsIso (Cocones.extend s f) :=
  ⟨(extendIso s (asIso f)).inv, by aesop_cat⟩

@[simps]
def precompose {G : J ⥤ C} (α : G ⟶ F) : Cocone F ⥤ Cocone G where
  obj c :=
    { pt := c.pt
      ι := α ≫ c.ι }
  map f := { hom := f.hom }

def precomposeComp {G H : J ⥤ C} (α : F ⟶ G) (β : G ⟶ H) :
    precompose (α ≫ β) ≅ precompose β ⋙ precompose α :=
  NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

def precomposeId : precompose (𝟙 F) ≅ 𝟭 (Cocone F) :=
  NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

@[simps]
def precomposeEquivalence {G : J ⥤ C} (α : G ≅ F) : Cocone F ≌ Cocone G where
  functor := precompose α.hom
  inverse := precompose α.inv
  unitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)

@[simps]
def whiskering (E : K ⥤ J) : Cocone F ⥤ Cocone (E ⋙ F) where
  obj c := c.whisker E
  map f := { hom := f.hom }

@[simps]
def whiskeringEquivalence (e : K ≌ J) : Cocone F ≌ Cocone (e.functor ⋙ F) where
  functor := whiskering e.functor
  inverse :=
    whiskering e.inverse ⋙
      precompose
        ((Functor.leftUnitor F).inv ≫
          whiskerRight e.counitIso.inv F ≫ (Functor.associator _ _ _).inv)
  unitIso := NatIso.ofComponents fun s => Cocones.ext (Iso.refl _)
  counitIso := NatIso.ofComponents fun s =>
    Cocones.ext (Iso.refl _) fun k => by simpa [e.counitInv_app_functor k] using s.w (e.unit.app k)

@[simps! functor_obj]
def equivalenceOfReindexing {G : K ⥤ C} (e : K ≌ J) (α : e.functor ⋙ F ≅ G) : Cocone F ≌ Cocone G :=
  (whiskeringEquivalence e).trans (precomposeEquivalence α.symm)

section

variable (F)

@[simps]
def forget : Cocone F ⥤ C where
  obj t := t.pt
  map f := f.hom

variable (G : C ⥤ D)

@[simps]
def functoriality : Cocone F ⥤ Cocone (F ⋙ G) where
  obj A :=
    { pt := G.obj A.pt
      ι :=
        { app := fun j => G.map (A.ι.app j)
          naturality := by intros; erw [← G.map_comp]; aesop_cat } }
  map f :=
    { hom := G.map f.hom
      w := by intros; rw [← Functor.map_comp, CoconeMorphism.w] }

instance functoriality_full [G.Full] [G.Faithful] : (functoriality F G).Full where
  map_surjective t :=
    ⟨{ hom := G.preimage t.hom
       w := fun j => G.map_injective (by simpa using t.w j) }, by aesop_cat⟩

instance functoriality_faithful [G.Faithful] : (functoriality F G).Faithful where
  map_injective {_X} {_Y} f g h :=
    CoconeMorphism.ext f g <| G.map_injective <| congr_arg CoconeMorphism.hom h

@[simps]
def functorialityEquivalence (e : C ≌ D) : Cocone F ≌ Cocone (F ⋙ e.functor) :=
  let f : (F ⋙ e.functor) ⋙ e.inverse ≅ F :=
    Functor.associator _ _ _ ≪≫ isoWhiskerLeft _ e.unitIso.symm ≪≫ Functor.rightUnitor _
  { functor := functoriality F e.functor
    inverse := functoriality (F ⋙ e.functor) e.inverse ⋙ (precomposeEquivalence f.symm).functor
    unitIso := NatIso.ofComponents fun c => Cocones.ext (e.unitIso.app _)
    counitIso := NatIso.ofComponents fun c => Cocones.ext (e.counitIso.app _) }

instance reflects_cocone_isomorphism (F : C ⥤ D) [F.ReflectsIsomorphisms] (K : J ⥤ C) :
    (Cocones.functoriality K F).ReflectsIsomorphisms := by
  constructor
  intro A B f _
  haveI : IsIso (F.map f.hom) :=
    (Cocones.forget (K ⋙ F)).map_isIso ((Cocones.functoriality K F).map f)
  haveI := ReflectsIsomorphisms.reflects F f.hom
  apply cocone_iso_of_hom_iso

end

end Cocones

end Limits

namespace Functor

variable (H : C ⥤ D) {F : J ⥤ C} {G : J ⥤ C}

open CategoryTheory.Limits

@[simps!]
def mapCone (c : Cone F) : Cone (F ⋙ H) :=
  (Cones.functoriality F H).obj c

@[simps!]
def mapCocone (c : Cocone F) : Cocone (F ⋙ H) :=
  (Cocones.functoriality F H).obj c

def mapConeMorphism {c c' : Cone F} (f : c ⟶ c') : H.mapCone c ⟶ H.mapCone c' :=
  (Cones.functoriality F H).map f

def mapCoconeMorphism {c c' : Cocone F} (f : c ⟶ c') : H.mapCocone c ⟶ H.mapCocone c' :=
  (Cocones.functoriality F H).map f

noncomputable def mapConeInv [IsEquivalence H] (c : Cone (F ⋙ H)) : Cone F :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).inverse.obj c

noncomputable def mapConeMapConeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cone (F ⋙ H)) :
    mapCone H (mapConeInv H c) ≅ c :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).counitIso.app c

noncomputable def mapConeInvMapCone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cone F) :
    mapConeInv H (mapCone H c) ≅ c :=
  (Limits.Cones.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

noncomputable def mapCoconeInv [IsEquivalence H] (c : Cocone (F ⋙ H)) : Cocone F :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).inverse.obj c

noncomputable def mapCoconeMapCoconeInv {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H]
    (c : Cocone (F ⋙ H)) :
    mapCocone H (mapCoconeInv H c) ≅ c :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).counitIso.app c

noncomputable def mapCoconeInvMapCocone {F : J ⥤ D} (H : D ⥤ C) [IsEquivalence H] (c : Cocone F) :
    mapCoconeInv H (mapCocone H c) ≅ c :=
  (Limits.Cocones.functorialityEquivalence F (asEquivalence H)).unitIso.symm.app c

@[simps!]
def functorialityCompPostcompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cones.functoriality F H ⋙ Cones.postcompose (whiskerLeft F α.hom) ≅ Cones.functoriality F H' :=
  NatIso.ofComponents fun c => Cones.ext (α.app _)

@[simps!]
def postcomposeWhiskerLeftMapCone {H H' : C ⥤ D} (α : H ≅ H') (c : Cone F) :
    (Cones.postcompose (whiskerLeft F α.hom : _)).obj (mapCone H c) ≅ mapCone H' c :=
  (functorialityCompPostcompose α).app c

@[simps!]
def mapConePostcompose {α : F ⟶ G} {c} :
    mapCone H ((Cones.postcompose α).obj c) ≅
      (Cones.postcompose (whiskerRight α H : _)).obj (mapCone H c) :=
  Cones.ext (Iso.refl _)

@[simps!]
def mapConePostcomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCone H ((Cones.postcomposeEquivalence α).functor.obj c) ≅
      (Cones.postcomposeEquivalence (isoWhiskerRight α H : _)).functor.obj (mapCone H c) :=
  Cones.ext (Iso.refl _)

@[simps!]
def functorialityCompPrecompose {H H' : C ⥤ D} (α : H ≅ H') :
    Cocones.functoriality F H ⋙ Cocones.precompose (whiskerLeft F α.inv) ≅
      Cocones.functoriality F H' :=
  NatIso.ofComponents fun c => Cocones.ext (α.app _)

@[simps!]
def precomposeWhiskerLeftMapCocone {H H' : C ⥤ D} (α : H ≅ H') (c : Cocone F) :
    (Cocones.precompose (whiskerLeft F α.inv : _)).obj (mapCocone H c) ≅ mapCocone H' c :=
  (functorialityCompPrecompose α).app c

@[simps!]
def mapCoconePrecompose {α : F ⟶ G} {c} :
    mapCocone H ((Cocones.precompose α).obj c) ≅
      (Cocones.precompose (whiskerRight α H : _)).obj (mapCocone H c) :=
  Cocones.ext (Iso.refl _)

@[simps!]
def mapCoconePrecomposeEquivalenceFunctor {α : F ≅ G} {c} :
    mapCocone H ((Cocones.precomposeEquivalence α).functor.obj c) ≅
      (Cocones.precomposeEquivalence (isoWhiskerRight α H : _)).functor.obj (mapCocone H c) :=
  Cocones.ext (Iso.refl _)

@[simps!]
def mapConeWhisker {E : K ⥤ J} {c : Cone F} : mapCone H (c.whisker E) ≅ (mapCone H c).whisker E :=
  Cones.ext (Iso.refl _)

@[simps!]
def mapCoconeWhisker {E : K ⥤ J} {c : Cocone F} :
    mapCocone H (c.whisker E) ≅ (mapCocone H c).whisker E :=
  Cocones.ext (Iso.refl _)

end Functor

end CategoryTheory

namespace CategoryTheory.Limits

section

variable {F : J ⥤ C}

@[simps]
def Cocone.op (c : Cocone F) : Cone F.op where
  pt := Opposite.op c.pt
  π := NatTrans.op c.ι

@[simps]
def Cone.op (c : Cone F) : Cocone F.op where
  pt := Opposite.op c.pt
  ι := NatTrans.op c.π

@[simps]
def Cocone.unop (c : Cocone F.op) : Cone F where
  pt := Opposite.unop c.pt
  π := NatTrans.removeOp c.ι

@[simps]
def Cone.unop (c : Cone F.op) : Cocone F where
  pt := Opposite.unop c.pt
  ι := NatTrans.removeOp c.π

variable (F)

def coconeEquivalenceOpConeOp : Cocone F ≌ (Cone F.op)ᵒᵖ where
  functor :=
    { obj := fun c => op (Cocone.op c)
      map := fun {X} {Y} f =>
        Quiver.Hom.op
          { hom := f.hom.op
            w := fun j => by
              apply Quiver.Hom.unop_inj
              dsimp
              apply CoconeMorphism.w } }
  inverse :=
    { obj := fun c => Cone.unop (unop c)
      map := fun {X} {Y} f =>
        { hom := f.unop.hom.unop
          w := fun j => by
            apply Quiver.Hom.op_inj
            dsimp
            apply ConeMorphism.w } }
  unitIso := NatIso.ofComponents (fun c => Cocones.ext (Iso.refl _))
  counitIso :=
    NatIso.ofComponents
      (fun c => by
        induction c
        apply Iso.op
        exact Cones.ext (Iso.refl _))
      fun {X} {Y} f =>
      Quiver.Hom.unop_inj (ConeMorphism.ext _ _ (by simp))
  functor_unitIso_comp c := by
    apply Quiver.Hom.unop_inj
    apply ConeMorphism.ext
    dsimp
    apply comp_id

attribute [simps] coconeEquivalenceOpConeOp

end

section

variable {F : J ⥤ Cᵒᵖ}

@[simps!]
def coneOfCoconeLeftOp (c : Cocone F.leftOp) : Cone F where
  pt := op c.pt
  π := NatTrans.removeLeftOp c.ι

@[simps!]
def coconeLeftOpOfCone (c : Cone F) : Cocone F.leftOp where
  pt := unop c.pt
  ι := NatTrans.leftOp c.π

@[simps pt]
def coconeOfConeLeftOp (c : Cone F.leftOp) : Cocone F where
  pt := op c.pt
  ι := NatTrans.removeLeftOp c.π

@[simp]
theorem coconeOfConeLeftOp_ι_app (c : Cone F.leftOp) (j) :
    (coconeOfConeLeftOp c).ι.app j = (c.π.app (op j)).op := by
  dsimp only [coconeOfConeLeftOp]
  simp

@[simps!]
def coneLeftOpOfCocone (c : Cocone F) : Cone F.leftOp where
  pt := unop c.pt
  π := NatTrans.leftOp c.ι

end

section

variable {F : Jᵒᵖ ⥤ C}

@[simps]
def coneOfCoconeRightOp (c : Cocone F.rightOp) : Cone F where
  pt := unop c.pt
  π := NatTrans.removeRightOp c.ι

@[simps]
def coconeRightOpOfCone (c : Cone F) : Cocone F.rightOp where
  pt := op c.pt
  ι := NatTrans.rightOp c.π

@[simps]
def coconeOfConeRightOp (c : Cone F.rightOp) : Cocone F where
  pt := unop c.pt
  ι := NatTrans.removeRightOp c.π

@[simps]
def coneRightOpOfCocone (c : Cocone F) : Cone F.rightOp where
  pt := op c.pt
  π := NatTrans.rightOp c.ι

end

section

variable {F : Jᵒᵖ ⥤ Cᵒᵖ}

@[simps]
def coneOfCoconeUnop (c : Cocone F.unop) : Cone F where
  pt := op c.pt
  π := NatTrans.removeUnop c.ι

@[simps]
def coconeUnopOfCone (c : Cone F) : Cocone F.unop where
  pt := unop c.pt
  ι := NatTrans.unop c.π

@[simps]
def coconeOfConeUnop (c : Cone F.unop) : Cocone F where
  pt := op c.pt
  ι := NatTrans.removeUnop c.π

@[simps]
def coneUnopOfCocone (c : Cocone F) : Cone F.unop where
  pt := unop c.pt
  π := NatTrans.unop c.ι

end

end CategoryTheory.Limits

namespace CategoryTheory.Functor

open CategoryTheory.Limits

variable {F : J ⥤ C}

section

variable (G : C ⥤ D)

@[simps!]
def mapConeOp (t : Cone F) : (mapCone G t).op ≅ mapCocone G.op t.op :=
  Cocones.ext (Iso.refl _)

@[simps!]
def mapCoconeOp {t : Cocone F} : (mapCocone G t).op ≅ mapCone G.op t.op :=
  Cones.ext (Iso.refl _)

end

end CategoryTheory.Functor
