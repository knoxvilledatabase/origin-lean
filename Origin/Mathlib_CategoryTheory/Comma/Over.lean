/-
Extracted from CategoryTheory/Comma/Over.lean
Genuine: 90 | Conflates: 0 | Dissolved: 0 | Infrastructure: 53
-/
import Origin.Core
import Mathlib.CategoryTheory.Comma.StructuredArrow.Basic
import Mathlib.CategoryTheory.Category.Cat

/-!
# Over and under categories

Over (and under) categories are special cases of comma categories.
* If `L` is the identity functor and `R` is a constant functor, then `Comma L R` is the "slice" or
  "over" category over the object `R` maps to.
* Conversely, if `L` is a constant functor and `R` is the identity functor, then `Comma L R` is the
  "coslice" or "under" category under the object `L` maps to.

## Tags

Comma, Slice, Coslice, Over, Under
-/

namespace CategoryTheory

universe v₁ v₂ u₁ u₂

variable {T : Type u₁} [Category.{v₁} T]

variable {D : Type u₂} [Category.{v₂} D]

def Over (X : T) :=
  CostructuredArrow (𝟭 T) X

instance (X : T) : Category (Over X) := commaCategory

instance Over.inhabited [Inhabited T] : Inhabited (Over (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Over

variable {X : T}

@[ext]
theorem OverMorphism.ext {X : T} {U V : Over X} {f g : U ⟶ V} (h : f.left = g.left) : f = g := by
  let ⟨_,b,_⟩ := f
  let ⟨_,e,_⟩ := g
  congr
  simp only [eq_iff_true_of_subsingleton]

@[simp]
theorem over_right (U : Over X) : U.right = ⟨⟨⟩⟩ := by simp only

@[simp]
theorem id_left (U : Over X) : CommaMorphism.left (𝟙 U) = 𝟙 U.left :=
  rfl

@[simp, reassoc]
theorem comp_left (a b c : Over X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).left = f.left ≫ g.left :=
  rfl

@[reassoc (attr := simp)]
theorem w {A B : Over X} (f : A ⟶ B) : f.left ≫ B.hom = A.hom := by have := f.w; aesop_cat

@[simps! left hom]
def mk {X Y : T} (f : Y ⟶ X) : Over X :=
  CostructuredArrow.mk f

def coeFromHom {X Y : T} : CoeOut (Y ⟶ X) (Over X) where coe := mk

section

attribute [local instance] coeFromHom

@[simp]
theorem coe_hom {X Y : T} (f : Y ⟶ X) : (f : Over X).hom = f :=
  rfl

end

@[simps!]
def homMk {U V : Over X} (f : U.left ⟶ V.left) (w : f ≫ V.hom = U.hom := by aesop_cat) : U ⟶ V :=
  CostructuredArrow.homMk f w

attribute [-simp, nolint simpNF] homMk_right_down_down

@[simps!]
def isoMk {f g : Over X} (hl : f.left ≅ g.left) (hw : hl.hom ≫ g.hom = f.hom := by aesop_cat) :
    f ≅ g :=
  CostructuredArrow.isoMk hl hw

attribute [-simp, nolint simpNF] isoMk_hom_right_down_down isoMk_inv_right_down_down

@[reassoc (attr := simp)]
lemma hom_left_inv_left {f g : Over X} (e : f ≅ g) :
    e.hom.left ≫ e.inv.left = 𝟙 f.left := by
  simp [← Over.comp_left]

@[reassoc (attr := simp)]
lemma inv_left_hom_left {f g : Over X} (e : f ≅ g) :
    e.inv.left ≫ e.hom.left = 𝟙 g.left := by
  simp [← Over.comp_left]

section

variable (X)

def forget : Over X ⥤ T :=
  Comma.fst _ _

end

@[simp]
theorem forget_obj {U : Over X} : (forget X).obj U = U.left :=
  rfl

@[simp]
theorem forget_map {U V : Over X} {f : U ⟶ V} : (forget X).map f = f.left :=
  rfl

@[simps]
def forgetCocone (X : T) : Limits.Cocone (forget X) :=
  { pt := X
    ι := { app := Comma.hom } }

def map {Y : T} (f : X ⟶ Y) : Over X ⥤ Over Y :=
  Comma.mapRight _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Over X} {g : U ⟶ V}

@[simp]
theorem map_obj_left : ((map f).obj U).left = U.left :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = U.hom ≫ f :=
  rfl

@[simp]
theorem map_map_left : ((map f).map g).left = g.left :=
  rfl

end

def mapIso {Y : T} (f : X ≅ Y) : Over X ≌ Over Y :=
  Comma.mapRightIso _ <| Discrete.natIso fun _ ↦ f

@[simp] lemma mapIso_functor {Y : T} (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl

@[simp] lemma mapIso_inverse {Y : T} (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

section coherences

/-!
This section proves various equalities between functors that
demonstrate, for instance, that over categories assemble into a
functor `mapFunctor : T ⥤ Cat`.

These equalities between functors are then converted to natural
isomorphisms using `eqToIso`. Such natural isomorphisms could be
obtained directly using `Iso.refl` but this method will have
better computational properties, when used, for instance, in
developing the theory of Beck-Chevalley transformations.
-/

theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ := by
  fapply Functor.ext
  · intro x
    dsimp [Over, Over.map, Comma.mapRight]
    simp only [Category.comp_id]
    exact rfl
  · intros x y u
    dsimp [Over, Over.map, Comma.mapRight]
    simp

@[simps!]
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ := eqToIso (mapId_eq Y)

theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) = (forget X) := by
  fapply Functor.ext
  · dsimp [Over, Over.map]; intro x; exact rfl
  · intros x y u; simp

def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget Y) ≅ (forget X) := eqToIso (mapForget_eq f)

@[simp]
theorem eqToHom_left {X : T} {U V : Over X} (e : U = V) :
    (eqToHom e).left = eqToHom (e ▸ rfl : U.left = V.left) := by
  subst e; rfl

theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map f) ⋙ (map g) := by
  fapply Functor.ext
  · simp [Over.map, Comma.mapRight]
  · intro U V k
    ext
    simp

@[simps!]
def mapComp {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) ≅ (map f) ⋙ (map g) := eqToIso (mapComp_eq f g)

@[simps!]
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

variable (T) in

@[simps] def mapFunctor : T ⥤ Cat where
  obj X := Cat.of (Over X)
  map := map
  map_id := mapId_eq
  map_comp := mapComp_eq

end coherences

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Over.homMk (inv ((forget X).map f))
      ((asIso ((forget X).map f)).inv_comp_eq.2 (Over.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])

noncomputable def mkIdTerminal : Limits.IsTerminal (mk (𝟙 X)) :=
  CostructuredArrow.mkIdTerminal

instance forget_faithful : (forget X).Faithful where

theorem epi_of_epi_left {f g : Over X} (k : f ⟶ g) [hk : Epi k.left] : Epi k :=
  (forget X).epi_of_epi_map hk

theorem mono_of_mono_left {f g : Over X} (k : f ⟶ g) [hk : Mono k.left] : Mono k :=
  (forget X).mono_of_mono_map hk

instance mono_left_of_mono {f g : Over X} (k : f ⟶ g) [Mono k] : Mono k.left := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : mk (m ≫ f.hom) ⟶ f := homMk l (by
        dsimp; rw [← Over.w k, ← Category.assoc, congrArg (· ≫ g.hom) a, Category.assoc])
  suffices l' = (homMk m : mk (m ≫ f.hom) ⟶ f) by apply congrArg CommaMorphism.left this
  rw [← cancel_mono k]
  ext
  apply a

section IteratedSlice

variable (f : Over X)

@[simps]
def iteratedSliceForward : Over f ⥤ Over f.left where
  obj α := Over.mk α.hom.left
  map κ := Over.homMk κ.left.left (by dsimp; rw [← Over.w κ]; rfl)

@[simps]
def iteratedSliceBackward : Over f.left ⥤ Over f where
  obj g := mk (homMk g.hom : mk (g.hom ≫ f.hom) ⟶ f)
  map α := homMk (homMk α.left (w_assoc α f.hom)) (OverMorphism.ext (w α))

@[simps]
def iteratedSliceEquiv : Over f ≌ Over f.left where
  functor := iteratedSliceForward f
  inverse := iteratedSliceBackward f
  unitIso := NatIso.ofComponents (fun g => Over.isoMk (Over.isoMk (Iso.refl _)))
  counitIso := NatIso.ofComponents (fun g => Over.isoMk (Iso.refl _))

theorem iteratedSliceForward_forget :
    iteratedSliceForward f ⋙ forget f.left = forget f ⋙ forget X :=
  rfl

theorem iteratedSliceBackward_forget_forget :
    iteratedSliceBackward f ⋙ forget f ⋙ forget X = forget f.left :=
  rfl

end IteratedSlice

@[simps]
def post (F : T ⥤ D) : Over X ⥤ Over (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Over.homMk (F.map f.left)
    (by simp only [Functor.id_obj, mk_left, Functor.const_obj_obj, mk_hom, ← F.map_comp, w])

lemma post_comp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

@[simps!]
def postComp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

@[simps]
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post F ⋙ map (e.app X) ⟶ post G where
  app Y := Over.homMk (e.app Y.left)

@[simps!]
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ⋙ map (e.hom.app X) ≅ post G :=
  NatIso.ofComponents (fun A ↦ Over.isoMk (e.app A.left))

variable (X) (F : T ⥤ D)

instance [F.Faithful] : (Over.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.left h)

instance [F.Faithful] [F.Full] : (Over.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.left
    have w : a ≫ B.hom = A.hom := F.map_injective <| by simpa [ha] using Over.w _
    exact ⟨Over.homMk a, by ext; simpa⟩

instance [F.Full] [F.EssSurj] : (Over.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨A', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.left
    obtain ⟨f, hf⟩ := F.map_surjective (e.hom ≫ B.hom)
    exact ⟨Over.mk f, ⟨Over.isoMk e⟩⟩

instance [F.IsEquivalence] : (Over.post (X := X) F).IsEquivalence where

@[simps]
def postEquiv (F : T ≌ D) : Over X ≌ Over (F.functor.obj X) where
  functor := Over.post F.functor
  inverse := Over.post (X := F.functor.obj X) F.inverse ⋙ Over.map (F.unitIso.inv.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.unitIso.app A.left))
  counitIso := NatIso.ofComponents (fun A ↦ Over.isoMk (F.counitIso.app A.left))

end Over

namespace CostructuredArrow

@[simps!]
def toOver (F : D ⥤ T) (X : T) : CostructuredArrow F X ⥤ Over X :=
  CostructuredArrow.pre F (𝟭 T) X

instance (F : D ⥤ T) (X : T) [F.Faithful] : (toOver F X).Faithful :=
  show (CostructuredArrow.pre _ _ _).Faithful from inferInstance

instance (F : D ⥤ T) (X : T) [F.Full] : (toOver F X).Full :=
  show (CostructuredArrow.pre _ _ _).Full from inferInstance

instance (F : D ⥤ T) (X : T) [F.EssSurj] : (toOver F X).EssSurj :=
  show (CostructuredArrow.pre _ _ _).EssSurj from inferInstance

instance isEquivalence_toOver (F : D ⥤ T) (X : T) [F.IsEquivalence] :
    (toOver F X).IsEquivalence :=
  CostructuredArrow.isEquivalence_pre _ _ _

end CostructuredArrow

def Under (X : T) :=
  StructuredArrow X (𝟭 T)

instance (X : T) : Category (Under X) := commaCategory

instance Under.inhabited [Inhabited T] : Inhabited (Under (default : T)) where
  default :=
    { left := default
      right := default
      hom := 𝟙 _ }

namespace Under

variable {X : T}

@[ext]
theorem UnderMorphism.ext {X : T} {U V : Under X} {f g : U ⟶ V} (h : f.right = g.right) :
    f = g := by
  let ⟨_,b,_⟩ := f; let ⟨_,e,_⟩ := g
  congr; simp only [eq_iff_true_of_subsingleton]

@[simp]
theorem under_left (U : Under X) : U.left = ⟨⟨⟩⟩ := by simp only

@[simp]
theorem id_right (U : Under X) : CommaMorphism.right (𝟙 U) = 𝟙 U.right :=
  rfl

@[simp]
theorem comp_right (a b c : Under X) (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).right = f.right ≫ g.right :=
  rfl

@[reassoc (attr := simp)]
theorem w {A B : Under X} (f : A ⟶ B) : A.hom ≫ f.right = B.hom := by have := f.w; aesop_cat

@[simps! right hom]
def mk {X Y : T} (f : X ⟶ Y) : Under X :=
  StructuredArrow.mk f

@[simps!]
def homMk {U V : Under X} (f : U.right ⟶ V.right) (w : U.hom ≫ f = V.hom := by aesop_cat) : U ⟶ V :=
  StructuredArrow.homMk f w

attribute [-simp, nolint simpNF] homMk_left_down_down

def isoMk {f g : Under X} (hr : f.right ≅ g.right)
    (hw : f.hom ≫ hr.hom = g.hom := by aesop_cat) : f ≅ g :=
  StructuredArrow.isoMk hr hw

@[simp]
theorem isoMk_hom_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).hom.right = hr.hom :=
  rfl

@[simp]
theorem isoMk_inv_right {f g : Under X} (hr : f.right ≅ g.right) (hw : f.hom ≫ hr.hom = g.hom) :
    (isoMk hr hw).inv.right = hr.inv :=
  rfl

@[reassoc (attr := simp)]
lemma hom_right_inv_right {f g : Under X} (e : f ≅ g) :
    e.hom.right ≫ e.inv.right = 𝟙 f.right := by
  simp [← Under.comp_right]

@[reassoc (attr := simp)]
lemma inv_right_hom_right {f g : Under X} (e : f ≅ g) :
    e.inv.right ≫ e.hom.right = 𝟙 g.right := by
  simp [← Under.comp_right]

section

variable (X)

def forget : Under X ⥤ T :=
  Comma.snd _ _

end

@[simp]
theorem forget_obj {U : Under X} : (forget X).obj U = U.right :=
  rfl

@[simp]
theorem forget_map {U V : Under X} {f : U ⟶ V} : (forget X).map f = f.right :=
  rfl

@[simps]
def forgetCone (X : T) : Limits.Cone (forget X) :=
  { pt := X
    π := { app := Comma.hom } }

def map {Y : T} (f : X ⟶ Y) : Under Y ⥤ Under X :=
  Comma.mapLeft _ <| Discrete.natTrans fun _ => f

section

variable {Y : T} {f : X ⟶ Y} {U V : Under Y} {g : U ⟶ V}

@[simp]
theorem map_obj_right : ((map f).obj U).right = U.right :=
  rfl

@[simp]
theorem map_obj_hom : ((map f).obj U).hom = f ≫ U.hom :=
  rfl

@[simp]
theorem map_map_right : ((map f).map g).right = g.right :=
  rfl

end

def mapIso {Y : T} (f : X ≅ Y) : Under Y ≌ Under X :=
  Comma.mapLeftIso _ <| Discrete.natIso fun _ ↦ f.symm

@[simp] lemma mapIso_functor {Y : T} (f : X ≅ Y) : (mapIso f).functor = map f.hom := rfl

@[simp] lemma mapIso_inverse {Y : T} (f : X ≅ Y) : (mapIso f).inverse = map f.inv := rfl

section coherences

/-!
This section proves various equalities between functors that
demonstrate, for instance, that under categories assemble into a
functor `mapFunctor : Tᵒᵖ ⥤ Cat`.
-/

theorem mapId_eq (Y : T) : map (𝟙 Y) = 𝟭 _ := by
  fapply Functor.ext
  · intro x
    dsimp [Under, Under.map, Comma.mapLeft]
    simp only [Category.id_comp]
    exact rfl
  · intros x y u
    dsimp [Under, Under.map, Comma.mapLeft]
    simp

@[simps!]
def mapId (Y : T) : map (𝟙 Y) ≅ 𝟭 _ := eqToIso (mapId_eq Y)

theorem mapForget_eq {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) = (forget Y) := by
  fapply Functor.ext
  · dsimp [Under, Under.map]; intro x; exact rfl
  · intros x y u; simp

def mapForget {X Y : T} (f : X ⟶ Y) :
    (map f) ⋙ (forget X) ≅ (forget Y) := eqToIso (mapForget_eq f)

@[simp]
theorem eqToHom_right {X : T} {U V : Under X} (e : U = V) :
    (eqToHom e).right = eqToHom (e ▸ rfl : U.right = V.right) := by
  subst e; rfl

theorem mapComp_eq {X Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) :
    map (f ≫ g) = (map g) ⋙ (map f) := by
  fapply Functor.ext
  · simp [Under.map, Comma.mapLeft]
  · intro U V k
    ext
    simp

@[simps!]
def mapComp {Y Z : T} (f : X ⟶ Y) (g : Y ⟶ Z) : map (f ≫ g) ≅ map g ⋙ map f :=
  eqToIso (mapComp_eq f g)

@[simps!]
def mapCongr {X Y : T} (f g : X ⟶ Y) (h : f = g) :
    map f ≅ map g :=
  NatIso.ofComponents (fun A ↦ eqToIso (by rw [h]))

variable (T) in

@[simps] def mapFunctor : Tᵒᵖ  ⥤ Cat where
  obj X := Cat.of (Under X.unop)
  map f := map f.unop
  map_id X := mapId_eq X.unop
  map_comp f g := mapComp_eq (g.unop) (f.unop)

end coherences

instance forget_reflects_iso : (forget X).ReflectsIsomorphisms where
  reflects {Y Z} f t := by
    let g : Z ⟶ Y := Under.homMk (inv ((Under.forget X).map f))
      ((IsIso.comp_inv_eq _).2 (Under.w f).symm)
    dsimp [forget] at t
    refine ⟨⟨g, ⟨?_,?_⟩⟩⟩
    repeat (ext; simp [g])

noncomputable def mkIdInitial : Limits.IsInitial (mk (𝟙 X)) :=
  StructuredArrow.mkIdInitial

instance forget_faithful : (forget X).Faithful where

theorem mono_of_mono_right {f g : Under X} (k : f ⟶ g) [hk : Mono k.right] : Mono k :=
  (forget X).mono_of_mono_map hk

theorem epi_of_epi_right {f g : Under X} (k : f ⟶ g) [hk : Epi k.right] : Epi k :=
  (forget X).epi_of_epi_map hk

instance epi_right_of_epi {f g : Under X} (k : f ⟶ g) [Epi k] : Epi k.right := by
  refine ⟨fun {Y : T} l m a => ?_⟩
  let l' : g ⟶ mk (g.hom ≫ m) := homMk l (by
    dsimp; rw [← Under.w k, Category.assoc, a, Category.assoc])
  -- Porting note: add type ascription here to `homMk m`
  suffices l' = (homMk m : g ⟶ mk (g.hom ≫ m)) by apply congrArg CommaMorphism.right this
  rw [← cancel_epi k]; ext; apply a

@[simps]
def post {X : T} (F : T ⥤ D) : Under X ⥤ Under (F.obj X) where
  obj Y := mk <| F.map Y.hom
  map f := Under.homMk (F.map f.right)
    (by simp only [Functor.id_obj, Functor.const_obj_obj, mk_right, mk_hom, ← F.map_comp, w])

lemma post_comp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) = post (X := X) F ⋙ post G :=
  rfl

@[simps!]
def postComp {E : Type*} [Category E] (F : T ⥤ D) (G : D ⥤ E) :
    post (X := X) (F ⋙ G) ≅ post F ⋙ post G :=
  NatIso.ofComponents (fun X ↦ Iso.refl _)

@[simps]
def postMap {F G : T ⥤ D} (e : F ⟶ G) : post (X := X) F ⟶ post G ⋙ map (e.app X) where
  app Y := Under.homMk (e.app Y.right)

@[simps!]
def postCongr {F G : T ⥤ D} (e : F ≅ G) : post F ≅ post G ⋙ map (e.hom.app X) :=
  NatIso.ofComponents (fun A ↦ Under.isoMk (e.app A.right))

variable (X) (F : T ⥤ D)

instance [F.Faithful] : (Under.post (X := X) F).Faithful where
  map_injective {A B} f g h := by
    ext
    exact F.map_injective (congrArg CommaMorphism.right h)

instance [F.Faithful] [F.Full] : (Under.post (X := X) F).Full where
  map_surjective {A B} f := by
    obtain ⟨a, ha⟩ := F.map_surjective f.right
    dsimp at a
    have w : A.hom ≫ a = B.hom := F.map_injective <| by simpa [ha] using Under.w f
    exact ⟨Under.homMk a, by ext; simpa⟩

instance [F.Full] [F.EssSurj] : (Under.post (X := X) F).EssSurj where
  mem_essImage B := by
    obtain ⟨B', ⟨e⟩⟩ := Functor.EssSurj.mem_essImage (F := F) B.right
    obtain ⟨f, hf⟩ := F.map_surjective (B.hom ≫ e.inv)
    exact ⟨Under.mk f, ⟨Under.isoMk e⟩⟩

instance [F.IsEquivalence] : (Under.post (X := X) F).IsEquivalence where

@[simps]
def postEquiv (F : T ≌ D) : Under X ≌ Under (F.functor.obj X) where
  functor := post F.functor
  inverse := post (X := F.functor.obj X) F.inverse ⋙ Under.map (F.unitIso.hom.app X)
  unitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.unitIso.app A.right))
  counitIso := NatIso.ofComponents (fun A ↦ Under.isoMk (F.counitIso.app A.right))

end Under

namespace StructuredArrow

variable {D : Type u₂} [Category.{v₂} D]

@[simps!]
def toUnder (X : T) (F : D ⥤ T) : StructuredArrow X F ⥤ Under X :=
  StructuredArrow.pre X F (𝟭 T)

instance (X : T) (F : D ⥤ T) [F.Faithful] : (toUnder X F).Faithful :=
  show (StructuredArrow.pre _ _ _).Faithful from inferInstance

instance (X : T) (F : D ⥤ T) [F.Full] : (toUnder X F).Full :=
  show (StructuredArrow.pre _ _ _).Full from inferInstance

instance (X : T) (F : D ⥤ T) [F.EssSurj] : (toUnder X F).EssSurj :=
  show (StructuredArrow.pre _ _ _).EssSurj from inferInstance

instance isEquivalence_toUnder (X : T) (F : D ⥤ T) [F.IsEquivalence] :
    (toUnder X F).IsEquivalence :=
  StructuredArrow.isEquivalence_pre _ _ _

end StructuredArrow

namespace Functor

variable {S : Type u₂} [Category.{v₂} S]

@[simps! obj_left map_left]
def toOver (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : S ⥤ Over X :=
  F.toCostructuredArrow (𝟭 _) X f h

def toOverCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma toOver_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → F.obj Y ⟶ X)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), F.map g ≫ f Z = f Y) : F.toOver X f h ⋙ Over.forget _ = F :=
  rfl

@[simps! obj_right map_right]
def toUnder (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : S ⥤ Under X :=
  F.toStructuredArrow X (𝟭 _) f h

def toUnderCompForget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ ≅ F :=
  Iso.refl _

@[simp]
lemma toUnder_comp_forget (F : S ⥤ T) (X : T) (f : (Y : S) → X ⟶ F.obj Y)
    (h : ∀ {Y Z : S} (g : Y ⟶ Z), f Y ≫ F.map g = f Z) : F.toUnder X f h ⋙ Under.forget _ = F :=
  rfl

end Functor

namespace StructuredArrow

@[simps!]
def ofStructuredArrowProjEquivalence.functor (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ⥤ StructuredArrow Y (Under.forget X ⋙ F) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _ ⋙ StructuredArrow.proj Y _) _
      (fun g => by exact g.hom) (fun m => by have := m.w; aesop_cat)) _ _
    (fun f => f.right.hom) (by simp)

@[simps!]
def ofStructuredArrowProjEquivalence.inverse (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow Y (Under.forget X ⋙ F) ⥤ StructuredArrow X (StructuredArrow.proj Y F) :=
  Functor.toStructuredArrow
    (Functor.toStructuredArrow (StructuredArrow.proj Y _ ⋙ Under.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; aesop_cat)) _ _
    (fun f => f.right.hom) (by simp)

def ofStructuredArrowProjEquivalence (F : D ⥤ T) (Y : T) (X : D) :
    StructuredArrow X (StructuredArrow.proj Y F) ≌ StructuredArrow Y (Under.forget X ⋙ F) where
  functor := ofStructuredArrowProjEquivalence.functor F Y X
  inverse := ofStructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

@[simps!]
def ofDiagEquivalence.functor (X : T × T) :
    StructuredArrow X (Functor.diag _) ⥤ StructuredArrow X.2 (Under.forget X.1) :=
  Functor.toStructuredArrow
    (Functor.toUnder (StructuredArrow.proj X _) _
      (fun f => by exact f.hom.1) (fun m => by have := m.w; aesop_cat)) _ _
    (fun f => f.hom.2) (fun m => by have := m.w; aesop_cat)

@[simps!]
def ofDiagEquivalence.inverse (X : T × T) :
    StructuredArrow X.2 (Under.forget X.1) ⥤ StructuredArrow X (Functor.diag _) :=
  Functor.toStructuredArrow (StructuredArrow.proj _ _ ⋙ Under.forget _) _ _
    (fun f => (f.right.hom, f.hom)) (fun m => by have := m.w; aesop_cat)

def ofDiagEquivalence (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.2 (Under.forget X.1) where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

def ofDiagEquivalence' (X : T × T) :
    StructuredArrow X (Functor.diag _) ≌ StructuredArrow X.1 (Under.forget X.2) :=
  (ofDiagEquivalence X).trans <|
    (ofStructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    StructuredArrow.mapNatIso (Under.forget X.2).rightUnitor

end StructuredArrow

namespace CostructuredArrow

@[simps!]
def ofCostructuredArrowProjEquivalence.functor (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X ⥤ CostructuredArrow (Over.forget X ⋙ F) Y :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X ⋙ CostructuredArrow.proj F Y) _
      (fun g => by exact g.hom) (fun m => by have := m.w; aesop_cat)) _ _
    (fun f => f.left.hom) (by simp)

@[simps!]
def ofCostructuredArrowProjEquivalence.inverse (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (Over.forget X ⋙ F) Y ⥤ CostructuredArrow (CostructuredArrow.proj F Y) X :=
  Functor.toCostructuredArrow
    (Functor.toCostructuredArrow (CostructuredArrow.proj _ Y ⋙ Over.forget X) _ _
      (fun g => by exact g.hom) (fun m => by have := m.w; aesop_cat)) _ _
    (fun f => f.left.hom) (by simp)

def ofCostructuredArrowProjEquivalence (F : T ⥤ D) (Y : D) (X : T) :
    CostructuredArrow (CostructuredArrow.proj F Y) X
      ≌ CostructuredArrow (Over.forget X ⋙ F) Y where
  functor := ofCostructuredArrowProjEquivalence.functor F Y X
  inverse := ofCostructuredArrowProjEquivalence.inverse F Y X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

@[simps!]
def ofDiagEquivalence.functor (X : T × T) :
    CostructuredArrow (Functor.diag _) X ⥤ CostructuredArrow (Over.forget X.1) X.2 :=
  Functor.toCostructuredArrow
    (Functor.toOver (CostructuredArrow.proj _ X) _
      (fun g => by exact g.hom.1) (fun m => by have := congrArg (·.1) m.w; aesop_cat))
    _ _
    (fun f => f.hom.2) (fun m => by have := congrArg (·.2) m.w; aesop_cat)

@[simps!]
def ofDiagEquivalence.inverse (X : T × T) :
    CostructuredArrow (Over.forget X.1) X.2 ⥤ CostructuredArrow (Functor.diag _) X :=
  Functor.toCostructuredArrow (CostructuredArrow.proj _ _ ⋙ Over.forget _) _ X
    (fun f => (f.left.hom, f.hom)) (fun m => by have := m.w; aesop_cat)

def ofDiagEquivalence (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.1) X.2 where
  functor := ofDiagEquivalence.functor X
  inverse := ofDiagEquivalence.inverse X
  unitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by simp)
  counitIso := NatIso.ofComponents (fun _ => Iso.refl _) (by aesop_cat)

def ofDiagEquivalence' (X : T × T) :
    CostructuredArrow (Functor.diag _) X ≌ CostructuredArrow (Over.forget X.2) X.1 :=
  (ofDiagEquivalence X).trans <|
    (ofCostructuredArrowProjEquivalence (𝟭 T) X.1 X.2).trans <|
    CostructuredArrow.mapNatIso (Over.forget X.2).rightUnitor

end CostructuredArrow

section Opposite

open Opposite

variable (X : T)

@[simps]
def Over.opToOpUnder : Over (op X) ⥤ (Under X)ᵒᵖ where
  obj Y := ⟨Under.mk Y.hom.unop⟩
  map {Z Y} f := ⟨Under.homMk (f.left.unop) (by dsimp; rw [← unop_comp, Over.w])⟩

@[simps]
def Under.opToOverOp : (Under X)ᵒᵖ ⥤ Over (op X) where
  obj Y := Over.mk (Y.unop.hom.op)
  map {Z Y} f := Over.homMk f.unop.right.op <| by dsimp; rw [← Under.w f.unop, op_comp]

@[simps]
def Over.opEquivOpUnder : Over (op X) ≌ (Under X)ᵒᵖ where
  functor := Over.opToOpUnder X
  inverse := Under.opToOverOp X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

@[simps]
def Under.opToOpOver : Under (op X) ⥤ (Over X)ᵒᵖ where
  obj Y := ⟨Over.mk Y.hom.unop⟩
  map {Z Y} f := ⟨Over.homMk (f.right.unop) (by dsimp; rw [← unop_comp, Under.w])⟩

@[simps]
def Over.opToUnderOp : (Over X)ᵒᵖ ⥤ Under (op X) where
  obj Y := Under.mk (Y.unop.hom.op)
  map {Z Y} f := Under.homMk f.unop.left.op <| by dsimp; rw [← Over.w f.unop, op_comp]

@[simps]
def Under.opEquivOpOver : Under (op X) ≌ (Over X)ᵒᵖ where
  functor := Under.opToOpOver X
  inverse := Over.opToUnderOp X
  unitIso := Iso.refl _
  counitIso := Iso.refl _

end Opposite

end CategoryTheory
