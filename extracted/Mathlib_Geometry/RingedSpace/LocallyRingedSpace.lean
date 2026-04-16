/-
Extracted from Geometry/RingedSpace/LocallyRingedSpace.lean
Genuine: 50 | Conflates: 0 | Dissolved: 0 | Infrastructure: 23
-/
import Origin.Core
import Mathlib.Algebra.Category.Ring.Constructions
import Mathlib.Geometry.RingedSpace.Basic
import Mathlib.Geometry.RingedSpace.Stalks
import Mathlib.RingTheory.Nilpotent.Defs

noncomputable section

/-!
# The category of locally ringed spaces

We define (bundled) locally ringed spaces (as `SheafedSpace CommRing` along with the fact that the
stalks are local rings), and morphisms between these (morphisms in `SheafedSpace` with
`IsLocalHom` on the stalk maps).
-/

universe u

open CategoryTheory

open TopCat

open TopologicalSpace Topology

open Opposite

open CategoryTheory.Category CategoryTheory.Functor

namespace AlgebraicGeometry

structure LocallyRingedSpace extends SheafedSpace CommRingCat.{u} where
  /-- Stalks of a locally ringed space are local rings. -/
  isLocalRing : ∀ x, IsLocalRing (presheaf.stalk x)

attribute [instance] LocallyRingedSpace.isLocalRing

namespace LocallyRingedSpace

variable (X : LocallyRingedSpace.{u})

def toRingedSpace : RingedSpace :=
  X.toSheafedSpace

def toTopCat : TopCat :=
  X.1.carrier

instance : CoeSort LocallyRingedSpace (Type u) :=
  ⟨fun X : LocallyRingedSpace => (X.toTopCat : Type _)⟩

instance (x : X) : IsLocalRing (X.presheaf.stalk x) :=
  X.isLocalRing x

def 𝒪 : Sheaf CommRingCat X.toTopCat :=
  X.sheaf

@[ext]
structure Hom (X Y : LocallyRingedSpace.{u})
    extends X.toPresheafedSpace.Hom Y.toPresheafedSpace : Type _ where
  /-- the underlying morphism induces a local ring homomorphism on stalks -/
  prop : ∀ x, IsLocalHom (toHom.stalkMap x)

abbrev Hom.toShHom {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y) :
  X.toSheafedSpace ⟶ Y.toSheafedSpace := f.1

@[simp, nolint simpVarHead]
lemma Hom.toShHom_mk {X Y : LocallyRingedSpace.{u}}
    (f : X.toPresheafedSpace.Hom Y.toPresheafedSpace) (hf) :
  Hom.toShHom ⟨f, hf⟩ = f := rfl

instance : Quiver LocallyRingedSpace :=
  ⟨Hom⟩

@[ext] lemma Hom.ext' {X Y : LocallyRingedSpace.{u}} {f g : X ⟶ Y} (h : f.toShHom = g.toShHom) :
    f = g := by cases f; cases g; congr

def Hom.Simps.toShHom {X Y : LocallyRingedSpace.{u}} (f : X.Hom Y) :
    X.toSheafedSpace ⟶ Y.toSheafedSpace :=
  f.toShHom

initialize_simps_projections Hom (toHom → toShHom)

noncomputable def Hom.stalkMap {X Y : LocallyRingedSpace.{u}} (f : Hom X Y) (x : X) :
    Y.presheaf.stalk (f.1.1 x) ⟶ X.presheaf.stalk x :=
  f.toShHom.stalkMap x

@[instance]
theorem isLocalHomStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.stalkMap x) :=
  f.2 x

@[instance]
theorem isLocalHomValStalkMap {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x : X) :
    IsLocalHom (f.toShHom.stalkMap x) :=
  f.2 x

alias isLocalRingHomValStalkMap := isLocalHomValStalkMap

@[simps! toShHom]
def id (X : LocallyRingedSpace.{u}) : Hom X X :=
  ⟨𝟙 X.toSheafedSpace, fun x => by erw [PresheafedSpace.stalkMap.id]; infer_instance⟩

instance (X : LocallyRingedSpace.{u}) : Inhabited (Hom X X) :=
  ⟨id X⟩

def comp {X Y Z : LocallyRingedSpace.{u}} (f : Hom X Y) (g : Hom Y Z) : Hom X Z :=
  ⟨f.toShHom ≫ g.toShHom, fun x => by
    erw [PresheafedSpace.stalkMap.comp]
    infer_instance⟩

instance : Category LocallyRingedSpace.{u} where
  Hom := Hom
  id := id
  comp {_ _ _} f g := comp f g
  comp_id {X Y} f := Hom.ext' <| by simp [comp]
  id_comp {X Y} f := Hom.ext' <| by simp [comp]
  assoc {_ _ _ _} f g h := Hom.ext' <| by simp [comp]

@[simps]
def forgetToSheafedSpace : LocallyRingedSpace.{u} ⥤ SheafedSpace CommRingCat.{u} where
  obj X := X.toSheafedSpace
  map {_ _} f := f.1

instance : forgetToSheafedSpace.Faithful where
  map_injective {_ _} _ _ h := Hom.ext' h

@[simps!]
def forgetToTop : LocallyRingedSpace.{u} ⥤ TopCat.{u} :=
  forgetToSheafedSpace ⋙ SheafedSpace.forget _

@[simp]
theorem comp_toShHom {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).toShHom = f.toShHom ≫ g.toShHom :=
  rfl

@[simp] theorem id_toShHom' (X : LocallyRingedSpace.{u}) :
    Hom.toShHom (𝟙 X) = 𝟙 X.toSheafedSpace :=
  rfl

theorem comp_base {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

@[simps! toShHom]
def homOfSheafedSpaceHomOfIsIso {X Y : LocallyRingedSpace.{u}}
    (f : X.toSheafedSpace ⟶ Y.toSheafedSpace) [IsIso f] : X ⟶ Y :=
  Hom.mk f fun _ =>
    -- Here we need to see that the stalk maps are really local ring homomorphisms.
    -- This can be solved by type class inference, because stalk maps of isomorphisms
    -- are isomorphisms and isomorphisms are local ring homomorphisms.
    inferInstance

def isoOfSheafedSpaceIso {X Y : LocallyRingedSpace.{u}} (f : X.toSheafedSpace ≅ Y.toSheafedSpace) :
    X ≅ Y where
  hom := homOfSheafedSpaceHomOfIsIso f.hom
  inv := homOfSheafedSpaceHomOfIsIso f.inv
  hom_inv_id := Hom.ext' f.hom_inv_id
  inv_hom_id := Hom.ext' f.inv_hom_id

instance : forgetToSheafedSpace.ReflectsIsomorphisms where reflects {_ _} f i :=
  { out :=
      ⟨homOfSheafedSpaceHomOfIsIso (CategoryTheory.inv (forgetToSheafedSpace.map f)),
        Hom.ext' (IsIso.hom_inv_id (I := i)), Hom.ext' (IsIso.inv_hom_id (I := i))⟩ }

instance is_sheafedSpace_iso {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) [IsIso f] :
    IsIso f.toShHom :=
  LocallyRingedSpace.forgetToSheafedSpace.map_isIso f

@[simps!]
def restrict {U : TopCat} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat}
    (h : IsOpenEmbedding f) : LocallyRingedSpace where
  isLocalRing := by
    intro x
    -- We show that the stalk of the restriction is isomorphic to the original stalk,
    apply @RingEquiv.isLocalRing _ _ _ (X.isLocalRing (f x))
    exact (X.restrictStalkIso h x).symm.commRingCatIsoToRingEquiv
  toSheafedSpace := X.toSheafedSpace.restrict h

def ofRestrict {U : TopCat} (X : LocallyRingedSpace.{u})
    {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f) : X.restrict h ⟶ X :=
  ⟨X.toPresheafedSpace.ofRestrict h, fun _ => inferInstance⟩

def restrictTopIso (X : LocallyRingedSpace.{u}) :
    X.restrict (Opens.isOpenEmbedding ⊤) ≅ X :=
  isoOfSheafedSpaceIso X.toSheafedSpace.restrictTopIso

def Γ : LocallyRingedSpace.{u}ᵒᵖ ⥤ CommRingCat.{u} :=
  forgetToSheafedSpace.op ⋙ SheafedSpace.Γ

@[simp]
theorem Γ_obj (X : LocallyRingedSpace.{u}ᵒᵖ) : Γ.obj X = X.unop.presheaf.obj (op ⊤) :=
  rfl

@[simp]
theorem Γ_map {X Y : LocallyRingedSpace.{u}ᵒᵖ} (f : X ⟶ Y) : Γ.map f = f.unop.c.app (op ⊤) :=
  rfl

def empty : LocallyRingedSpace.{u} where
  carrier := TopCat.of PEmpty
  presheaf := (CategoryTheory.Functor.const _).obj (CommRingCat.of PUnit)
  IsSheaf := Presheaf.isSheaf_of_isTerminal _ CommRingCat.punitIsTerminal
  isLocalRing x := PEmpty.elim x

instance : EmptyCollection LocallyRingedSpace.{u} := ⟨LocallyRingedSpace.empty⟩

def emptyTo (X : LocallyRingedSpace) : ∅ ⟶ X :=
  ⟨⟨⟨fun x => PEmpty.elim x, by fun_prop⟩,
    { app := fun U => by refine ⟨⟨⟨0, ?_⟩, ?_⟩, ?_, ?_⟩ <;> intros <;> rfl }⟩,
    fun x => PEmpty.elim x⟩

noncomputable
instance {X : LocallyRingedSpace} : Unique (∅ ⟶ X) where
  default := LocallyRingedSpace.emptyTo X
  uniq f := by ext ⟨⟩ x; aesop_cat

noncomputable
def emptyIsInitial : Limits.IsInitial (∅ : LocallyRingedSpace.{u}) := Limits.IsInitial.ofUnique _

theorem basicOpen_zero (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) :
    X.toRingedSpace.basicOpen (0 : X.presheaf.obj <| op U) = ⊥ := by
  ext x
  simp only [RingedSpace.basicOpen, Opens.coe_mk, Set.mem_image, Set.mem_setOf_eq, Subtype.exists,
    exists_and_right, exists_eq_right, Opens.coe_bot, Set.mem_empty_iff_false,
    iff_false, not_exists]
  intros hx
  rw [map_zero, isUnit_zero_iff]
  change (0 : X.presheaf.stalk x) ≠ (1 : X.presheaf.stalk x)
  exact zero_ne_one

@[simp]
lemma basicOpen_eq_bot_of_isNilpotent (X : LocallyRingedSpace.{u}) (U : Opens X.carrier)
    (f : (X.presheaf.obj <| op U)) (hf : IsNilpotent f) :
    X.toRingedSpace.basicOpen f = ⊥ := by
  obtain ⟨n, hn⟩ := hf
  cases n.eq_zero_or_pos with
  | inr h =>
    rw [←  X.toRingedSpace.basicOpen_pow f n h, hn]
    simp [basicOpen_zero]
  | inl h =>
    rw [h, pow_zero] at hn
    simp [eq_zero_of_zero_eq_one hn.symm f, basicOpen_zero]

instance component_nontrivial (X : LocallyRingedSpace.{u}) (U : Opens X.carrier) [hU : Nonempty U] :
    Nontrivial (X.presheaf.obj <| op U) :=
  (X.presheaf.germ _ _ hU.some.2).domain_nontrivial

@[simp]
lemma iso_hom_base_inv_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.hom.base ≫ e.inv.base = 𝟙 _ := by
  rw [← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_toShHom]
  simp

@[simp]
lemma iso_hom_base_inv_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (x : X) :
    (e.inv.base (e.hom.base x)) = x := by
  show (e.hom.base ≫ e.inv.base) x = 𝟙 X.toPresheafedSpace x
  simp

@[simp]
lemma iso_inv_base_hom_base {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) :
    e.inv.base ≫ e.hom.base = 𝟙 _ := by
  rw [← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_toShHom]
  simp

@[simp]
lemma iso_inv_base_hom_base_apply {X Y : LocallyRingedSpace.{u}} (e : X ≅ Y) (y : Y) :
    (e.hom.base (e.inv.base y)) = y := by
  show (e.inv.base ≫ e.hom.base) y = 𝟙 Y.toPresheafedSpace y
  simp

section Stalks

variable {X Y Z : LocallyRingedSpace.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

@[simp]
lemma stalkMap_id (X : LocallyRingedSpace.{u}) (x : X) :
    (𝟙 X : X ⟶ X).stalkMap x = 𝟙 (X.presheaf.stalk x) :=
  PresheafedSpace.stalkMap.id _ x

lemma stalkMap_comp (x : X) :
    (f ≫ g : X ⟶ Z).stalkMap x = g.stalkMap (f.base x) ≫ f.stalkMap x :=
  PresheafedSpace.stalkMap.comp f.toShHom g.toShHom x

@[reassoc]
lemma stalkSpecializes_stalkMap (x x' : X) (h : x ⤳ x') :
    Y.presheaf.stalkSpecializes (f.base.map_specializes h) ≫ f.stalkMap x =
      f.stalkMap x' ≫ X.presheaf.stalkSpecializes h :=
  PresheafedSpace.stalkMap.stalkSpecializes_stalkMap f.toShHom h

lemma stalkSpecializes_stalkMap_apply (x x' : X) (h : x ⤳ x') (y) :
    f.stalkMap x (Y.presheaf.stalkSpecializes (f.base.map_specializes h) y) =
      (X.presheaf.stalkSpecializes h (f.stalkMap x' y)) :=
  DFunLike.congr_fun (stalkSpecializes_stalkMap f x x' h) y

@[reassoc]
lemma stalkMap_congr (f g : X ⟶ Y) (hfg : f = g) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ hxx' ▸ rfl) ≫ g.stalkMap x' := by
  subst hfg
  subst hxx'
  simp

@[reassoc]
lemma stalkMap_congr_hom (f g : X ⟶ Y) (hfg : f = g) (x : X) :
    f.stalkMap x = Y.presheaf.stalkSpecializes (specializes_of_eq <| hfg ▸ rfl) ≫
      g.stalkMap x := by
  subst hfg
  simp

@[reassoc]
lemma stalkMap_congr_point {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) (x x' : X) (hxx' : x = x') :
    f.stalkMap x ≫ X.presheaf.stalkSpecializes (specializes_of_eq hxx'.symm) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| hxx' ▸ rfl) ≫ f.stalkMap x' := by
  subst hxx'
  simp

@[reassoc (attr := simp)]
lemma stalkMap_hom_inv (e : X ≅ Y) (y : Y) :
    e.hom.stalkMap (e.inv.base y) ≫ e.inv.stalkMap y =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.inv ≫ e.hom) (𝟙 _) (by simp)]
  simp

@[simp]
lemma stalkMap_hom_inv_apply (e : X ≅ Y) (y : Y) (z) :
    e.inv.stalkMap y (e.hom.stalkMap (e.inv.base y) z) =
      Y.presheaf.stalkSpecializes (specializes_of_eq <| by simp) z :=
  DFunLike.congr_fun (stalkMap_hom_inv e y) z

@[reassoc (attr := simp)]
lemma stalkMap_inv_hom (e : X ≅ Y) (x : X) :
    e.inv.stalkMap (e.hom.base x) ≫ e.hom.stalkMap x =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) := by
  rw [← stalkMap_comp, LocallyRingedSpace.stalkMap_congr_hom (e.hom ≫ e.inv) (𝟙 _) (by simp)]
  simp

@[simp]
lemma stalkMap_inv_hom_apply (e : X ≅ Y) (x : X) (y) :
    e.hom.stalkMap x (e.inv.stalkMap (e.hom.base x) y) =
      X.presheaf.stalkSpecializes (specializes_of_eq <| by simp) y :=
  DFunLike.congr_fun (stalkMap_inv_hom e x) y

@[reassoc (attr := simp)]
lemma stalkMap_germ (U : Opens Y) (x : X) (hx : f.base x ∈ U) :
    Y.presheaf.germ U (f.base x) hx ≫ f.stalkMap x =
      f.c.app (op U) ≫ X.presheaf.germ ((Opens.map f.base).obj U) x hx :=
  PresheafedSpace.stalkMap_germ f.toShHom U x hx

lemma stalkMap_germ_apply (U : Opens Y) (x : X) (hx : f.base x ∈ U) (y) :
    f.stalkMap x (Y.presheaf.germ U (f.base x) hx y) =
      X.presheaf.germ ((Opens.map f.base).obj U) x hx (f.c.app (op U) y) :=
  PresheafedSpace.stalkMap_germ_apply f.toShHom U x hx y

theorem preimage_basicOpen {X Y : LocallyRingedSpace.{u}} (f : X ⟶ Y) {U : Opens Y}
    (s : Y.presheaf.obj (op U)) :
    (Opens.map f.base).obj (Y.toRingedSpace.basicOpen s) =
      @RingedSpace.basicOpen X.toRingedSpace ((Opens.map f.base).obj U) (f.c.app _ s) := by
  ext x
  constructor
  · rintro ⟨hxU, hx⟩
    rw [SetLike.mem_coe, X.toRingedSpace.mem_basicOpen _ _ hxU]
    delta toRingedSpace
    rw [← stalkMap_germ_apply]
    exact (f.stalkMap _).isUnit_map hx
  · rintro ⟨hxU, hx⟩
    simp only [Opens.map_coe, Set.mem_preimage, SetLike.mem_coe, toRingedSpace] at hx ⊢
    rw [RingedSpace.mem_basicOpen _ s (f.base x) hxU]
    rw [← stalkMap_germ_apply] at hx
    exact (isUnit_map_iff (f.toShHom.stalkMap _) _).mp hx

variable {U : TopCat} (X : LocallyRingedSpace.{u}) {f : U ⟶ X.toTopCat} (h : IsOpenEmbedding f)
  (V : Opens U) (x : U) (hx : x ∈ V)

noncomputable
def restrictStalkIso : (X.restrict h).presheaf.stalk x ≅ X.presheaf.stalk (f x) :=
  X.toPresheafedSpace.restrictStalkIso h x

@[reassoc (attr := simp)]
lemma restrictStalkIso_hom_eq_germ :
    (X.restrict h).presheaf.germ _ x hx ≫ (X.restrictStalkIso h x).hom =
      X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ X.toPresheafedSpace h V x hx

lemma restrictStalkIso_hom_eq_germ_apply (y) :
    (X.restrictStalkIso h x).hom ((X.restrict h).presheaf.germ _ x hx y) =
      X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ y :=
  PresheafedSpace.restrictStalkIso_hom_eq_germ_apply X.toPresheafedSpace h V x hx y

@[reassoc (attr := simp)]
lemma restrictStalkIso_inv_eq_germ :
    X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ ≫
      (X.restrictStalkIso h x).inv = (X.restrict h).presheaf.germ _ x hx :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ X.toPresheafedSpace h V x hx

lemma restrictStalkIso_inv_eq_germ_apply (y) :
    (X.restrictStalkIso h x).inv
      (X.presheaf.germ (h.isOpenMap.functor.obj V) (f x) ⟨x, hx, rfl⟩ y) =
        (X.restrict h).presheaf.germ _ x hx y :=
  PresheafedSpace.restrictStalkIso_inv_eq_germ_apply X.toPresheafedSpace h V x hx y

lemma restrictStalkIso_inv_eq_ofRestrict :
    (X.restrictStalkIso h x).inv = (X.ofRestrict h).stalkMap x :=
  PresheafedSpace.restrictStalkIso_inv_eq_ofRestrict X.toPresheafedSpace h x

instance ofRestrict_stalkMap_isIso : IsIso ((X.ofRestrict h).stalkMap x) :=
  PresheafedSpace.ofRestrict_stalkMap_isIso X.toPresheafedSpace h x

end Stalks

end LocallyRingedSpace

end AlgebraicGeometry
