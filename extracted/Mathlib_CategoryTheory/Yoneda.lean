/-
Extracted from CategoryTheory/Yoneda.lean
Genuine: 87 | Conflates: 0 | Dissolved: 0 | Infrastructure: 22
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.Hom
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.Data.ULift
import Mathlib.Logic.Function.ULift

noncomputable section

/-!
# The Yoneda embedding

The Yoneda embedding as a functor `yoneda : C ⥤ (Cᵒᵖ ⥤ Type v₁)`,
along with an instance that it is `FullyFaithful`.

Also the Yoneda lemma, `yonedaLemma : (yoneda_pairing C) ≅ (yoneda_evaluation C)`.

## References
* [Stacks: Opposite Categories and the Yoneda Lemma](https://stacks.math.columbia.edu/tag/001L)
-/

namespace CategoryTheory

open Opposite

universe v v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]

@[simps]
def yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁ where
  obj X :=
    { obj := fun Y => unop Y ⟶ X
      map := fun f g => f.unop ≫ g }
  map f :=
    { app := fun _ g => g ≫ f }

@[simps]
def coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁ where
  obj X :=
    { obj := fun Y => unop X ⟶ Y
      map := fun f g => g ≫ f }
  map f :=
    { app := fun _ g => f.unop ≫ g }

namespace Yoneda

theorem obj_map_id {X Y : C} (f : op X ⟶ op Y) :
    (yoneda.obj X).map f (𝟙 X) = (yoneda.map f.unop).app (op Y) (𝟙 Y) := by
  dsimp
  simp

@[simp]
theorem naturality {X Y : C} (α : yoneda.obj X ⟶ yoneda.obj Y) {Z Z' : C} (f : Z ⟶ Z')
    (h : Z' ⟶ X) : f ≫ α.app (op Z') h = α.app (op Z) (f ≫ h) :=
  (FunctorToTypes.naturality _ _ α f.op h).symm

def fullyFaithful : (yoneda (C := C)).FullyFaithful where
  preimage f := f.app _ (𝟙 _)

instance yoneda_full : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Full :=
  fullyFaithful.full

instance yoneda_faithful : (yoneda : C ⥤ Cᵒᵖ ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

def ext (X Y : C) (p : ∀ {Z : C}, (Z ⟶ X) → (Z ⟶ Y))
    (q : ∀ {Z : C}, (Z ⟶ Y) → (Z ⟶ X))
    (h₁ : ∀ {Z : C} (f : Z ⟶ X), q (p f) = f) (h₂ : ∀ {Z : C} (f : Z ⟶ Y), p (q f) = f)
    (n : ∀ {Z Z' : C} (f : Z' ⟶ Z) (g : Z ⟶ X), p (f ≫ g) = f ≫ p g) : X ≅ Y :=
  fullyFaithful.preimageIso
    (NatIso.ofComponents fun Z =>
      { hom := p
        inv := q })

theorem isIso {X Y : C} (f : X ⟶ Y) [IsIso (yoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful yoneda f

end Yoneda

namespace Coyoneda

@[simp]
theorem naturality {X Y : Cᵒᵖ} (α : coyoneda.obj X ⟶ coyoneda.obj Y) {Z Z' : C} (f : Z' ⟶ Z)
    (h : unop X ⟶ Z') : α.app Z' h ≫ f = α.app Z (h ≫ f) :=
  (FunctorToTypes.naturality _ _ α f h).symm

def fullyFaithful : (coyoneda (C := C)).FullyFaithful where
  preimage f := (f.app _ (𝟙 _)).op

def preimage {X Y : Cᵒᵖ} (f : coyoneda.obj X ⟶ coyoneda.obj Y) : X ⟶ Y :=
  (f.app _ (𝟙 X.unop)).op

instance coyoneda_full : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Full :=
  fullyFaithful.full

instance coyoneda_faithful : (coyoneda : Cᵒᵖ ⥤ C ⥤ Type v₁).Faithful :=
  fullyFaithful.faithful

theorem isIso {X Y : Cᵒᵖ} (f : X ⟶ Y) [IsIso (coyoneda.map f)] : IsIso f :=
  isIso_of_fully_faithful coyoneda f

def punitIso : coyoneda.obj (Opposite.op PUnit) ≅ 𝟭 (Type v₁) :=
  NatIso.ofComponents fun X =>
    { hom := fun f => f ⟨⟩
      inv := fun x _ => x }

@[simps!]
def objOpOp (X : C) : coyoneda.obj (op (op X)) ≅ yoneda.obj X :=
  NatIso.ofComponents fun _ => (opEquiv _ _).toIso

end Coyoneda

namespace Functor

structure RepresentableBy (F : Cᵒᵖ ⥤ Type v) (Y : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj (op X)`. -/
  homEquiv {X : C} : (X ⟶ Y) ≃ F.obj (op X)
  homEquiv_comp {X X' : C} (f : X ⟶ X') (g : X' ⟶ Y) :
    homEquiv (f ≫ g) = F.map f.op (homEquiv g)

def RepresentableBy.ofIso {F F' : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) (e' : F ≅ F') :
    F'.RepresentableBy Y where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {X X'} f g := by
    dsimp
    rw [e.homEquiv_comp]
    apply congr_fun (e'.hom.naturality f.op)

structure CorepresentableBy (F : C ⥤ Type v) (X : C) where
  /-- the natural bijection `(X ⟶ Y) ≃ F.obj Y`. -/
  homEquiv {Y : C} : (X ⟶ Y) ≃ F.obj Y
  homEquiv_comp {Y Y' : C} (g : Y ⟶ Y') (f : X ⟶ Y) :
    homEquiv (f ≫ g) = F.map g (homEquiv f)

def CorepresentableBy.ofIso {F F' : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    (e' : F ≅ F') :
    F'.CorepresentableBy X where
  homEquiv {X} := e.homEquiv.trans (e'.app _).toEquiv
  homEquiv_comp {Y Y'} g f := by
    dsimp
    rw [e.homEquiv_comp]
    apply congr_fun (e'.hom.naturality g)

lemma RepresentableBy.homEquiv_eq {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y)
    {X : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f.op (e.homEquiv (𝟙 Y)) := by
  conv_lhs => rw [← Category.comp_id f, e.homEquiv_comp]

lemma CorepresentableBy.homEquiv_eq {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X)
    {Y : C} (f : X ⟶ Y) :
    e.homEquiv f = F.map f (e.homEquiv (𝟙 X)) := by
  conv_lhs => rw [← Category.id_comp f, e.homEquiv_comp]

@[ext]
lemma RepresentableBy.ext {F : Cᵒᵖ ⥤ Type v} {Y : C} {e e' : F.RepresentableBy Y}
    (h : e.homEquiv (𝟙 Y) = e'.homEquiv (𝟙 Y)) : e = e' := by
  have : ∀ {X : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

@[ext]
lemma CorepresentableBy.ext {F : C ⥤ Type v} {X : C} {e e' : F.CorepresentableBy X}
    (h : e.homEquiv (𝟙 X) = e'.homEquiv (𝟙 X)) : e = e' := by
  have : ∀ {Y : C} (f : X ⟶ Y), e.homEquiv f = e'.homEquiv f := fun {X} f ↦ by
    rw [e.homEquiv_eq, e'.homEquiv_eq, h]
  obtain ⟨e, he⟩ := e
  obtain ⟨e', he'⟩ := e'
  obtain rfl : @e = @e' := by ext; apply this
  rfl

def representableByEquiv {F : Cᵒᵖ ⥤ Type v₁} {Y : C} :
    F.RepresentableBy Y ≃ (yoneda.obj Y ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    simp [r.homEquiv_comp])
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ congr_fun (e.hom.naturality f.op) g }
  left_inv _ := rfl
  right_inv _ := rfl

def RepresentableBy.toIso {F : Cᵒᵖ ⥤ Type v₁} {Y : C} (e : F.RepresentableBy Y) :
    yoneda.obj Y ≅ F :=
  representableByEquiv e

def corepresentableByEquiv {F : C ⥤ Type v₁} {X : C} :
    F.CorepresentableBy X ≃ (coyoneda.obj (op X) ≅ F) where
  toFun r := NatIso.ofComponents (fun _ ↦ r.homEquiv.toIso) (fun {X X'} f ↦ by
    ext g
    simp [r.homEquiv_comp])
  invFun e :=
    { homEquiv := (e.app _).toEquiv
      homEquiv_comp := fun {X X'} f g ↦ congr_fun (e.hom.naturality f) g }
  left_inv _ := rfl
  right_inv _ := rfl

def CorepresentableBy.toIso {F : C ⥤ Type v₁} {X : C} (e : F.CorepresentableBy X) :
    coyoneda.obj (op X) ≅ F :=
  corepresentableByEquiv e

class IsRepresentable (F : Cᵒᵖ ⥤ Type v) : Prop where
  has_representation : ∃ (Y : C), Nonempty (F.RepresentableBy Y)

lemma RepresentableBy.isRepresentable {F : Cᵒᵖ ⥤ Type v} {Y : C} (e : F.RepresentableBy Y) :
    F.IsRepresentable where
  has_representation := ⟨Y, ⟨e⟩⟩

lemma IsRepresentable.mk' {F : Cᵒᵖ ⥤ Type v₁} {X : C} (e : yoneda.obj X ≅ F) :
    F.IsRepresentable :=
  (representableByEquiv.symm e).isRepresentable

instance {X : C} : IsRepresentable (yoneda.obj X) :=
  IsRepresentable.mk' (Iso.refl _)

class IsCorepresentable (F : C ⥤ Type v) : Prop where
  has_corepresentation : ∃ (X : C), Nonempty (F.CorepresentableBy X)

lemma CorepresentableBy.isCorepresentable {F : C ⥤ Type v} {X : C} (e : F.CorepresentableBy X) :
    F.IsCorepresentable where
  has_corepresentation := ⟨X, ⟨e⟩⟩

lemma IsCorepresentable.mk' {F : C ⥤ Type v₁} {X : C} (e : coyoneda.obj (op X) ≅ F) :
    F.IsCorepresentable :=
  (corepresentableByEquiv.symm e).isCorepresentable

instance {X : Cᵒᵖ} : IsCorepresentable (coyoneda.obj X) :=
  IsCorepresentable.mk' (Iso.refl _)

section Representable

variable (F : Cᵒᵖ ⥤ Type v) [hF : F.IsRepresentable]

noncomputable def reprX : C :=
  hF.has_representation.choose

noncomputable def representableBy : F.RepresentableBy F.reprX :=
  hF.has_representation.choose_spec.some

noncomputable def reprx : F.obj (op F.reprX) :=
  F.representableBy.homEquiv (𝟙 _)

noncomputable def reprW (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable] :
    yoneda.obj F.reprX ≅ F := F.representableBy.toIso

theorem reprW_hom_app (F : Cᵒᵖ ⥤ Type v₁) [F.IsRepresentable]
    (X : Cᵒᵖ) (f : unop X ⟶ F.reprX) :
    F.reprW.hom.app X f = F.map f.op F.reprx := by
  apply RepresentableBy.homEquiv_eq

end Representable

section Corepresentable

variable (F : C ⥤ Type v) [hF : F.IsCorepresentable]

noncomputable def coreprX : C :=
  hF.has_corepresentation.choose

noncomputable def corepresentableBy : F.CorepresentableBy F.coreprX :=
  hF.has_corepresentation.choose_spec.some

noncomputable def coreprx : F.obj F.coreprX :=
  F.corepresentableBy.homEquiv (𝟙 _)

noncomputable def coreprW (F : C ⥤ Type v₁) [F.IsCorepresentable] :
    coyoneda.obj (op F.coreprX) ≅ F :=
  F.corepresentableBy.toIso

theorem coreprW_hom_app (F : C ⥤ Type v₁) [F.IsCorepresentable] (X : C) (f : F.coreprX ⟶ X) :
    F.coreprW.hom.app X f = F.map f F.coreprx := by
  apply CorepresentableBy.homEquiv_eq

end Corepresentable

end Functor

theorem isRepresentable_of_natIso (F : Cᵒᵖ ⥤ Type v₁) {G} (i : F ≅ G) [F.IsRepresentable] :
    G.IsRepresentable :=
  (F.representableBy.ofIso i).isRepresentable

theorem corepresentable_of_natIso (F : C ⥤ Type v₁) {G} (i : F ≅ G) [F.IsCorepresentable] :
    G.IsCorepresentable :=
  (F.corepresentableBy.ofIso i).isCorepresentable

instance : Functor.IsCorepresentable (𝟭 (Type v₁)) :=
  corepresentable_of_natIso (coyoneda.obj (op PUnit)) Coyoneda.punitIso

open Opposite

variable (C)

instance prodCategoryInstance1 : Category ((Cᵒᵖ ⥤ Type v₁) × Cᵒᵖ) :=
  CategoryTheory.prod.{max u₁ v₁, v₁} (Cᵒᵖ ⥤ Type v₁) Cᵒᵖ

instance prodCategoryInstance2 : Category (Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) :=
  CategoryTheory.prod.{v₁, max u₁ v₁} Cᵒᵖ (Cᵒᵖ ⥤ Type v₁)

open Yoneda

section YonedaLemma

variable {C}

def yonedaEquiv {X : C} {F : Cᵒᵖ ⥤ Type v₁} : (yoneda.obj X ⟶ F) ≃ F.obj (op X) where
  toFun η := η.app (op X) (𝟙 X)
  invFun ξ := { app := fun _ f ↦ F.map f.op ξ }
  left_inv := by
    intro η
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    simp
  right_inv := by intro ξ; simp

theorem yonedaEquiv_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F) :
    yonedaEquiv f = f.app (op X) (𝟙 X) :=
  rfl

@[simp]
theorem yonedaEquiv_symm_app_apply {X : C} {F : Cᵒᵖ ⥤ Type v₁} (x : F.obj (op X)) (Y : Cᵒᵖ)
    (f : Y.unop ⟶ X) : (yonedaEquiv.symm x).app Y f = F.map f.op x :=
  rfl

lemma yonedaEquiv_naturality {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = yonedaEquiv (yoneda.map g ≫ f) := by
  change (f.app (op X) ≫ F.map g.op) (𝟙 X) = f.app (op Y) (𝟙 Y ≫ g)
  rw [← f.naturality]
  dsimp
  simp

lemma yonedaEquiv_naturality' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = yonedaEquiv (yoneda.map g.unop ≫ f) :=
  yonedaEquiv_naturality _ _

lemma yonedaEquiv_comp {X : C} {F G : Cᵒᵖ ⥤ Type v₁} (α : yoneda.obj X ⟶ F) (β : F ⟶ G) :
    yonedaEquiv (α ≫ β) = β.app _ (yonedaEquiv α) :=
  rfl

lemma yonedaEquiv_yoneda_map {X Y : C} (f : X ⟶ Y) : yonedaEquiv (yoneda.map f) = f := by
  rw [yonedaEquiv_apply]
  simp

lemma yonedaEquiv_symm_naturality_left {X X' : C} (f : X' ⟶ X) (F : Cᵒᵖ ⥤ Type v₁)
    (x : F.obj ⟨X⟩) : yoneda.map f ≫ yonedaEquiv.symm x = yonedaEquiv.symm ((F.map f.op) x) := by
  apply yonedaEquiv.injective
  simp only [yonedaEquiv_comp, yoneda_obj_obj, yonedaEquiv_symm_app_apply, Equiv.apply_symm_apply]
  erw [yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_naturality_right (X : C) {F F' : Cᵒᵖ ⥤ Type v₁} (f : F ⟶ F')
    (x : F.obj ⟨X⟩) : yonedaEquiv.symm x ≫ f = yonedaEquiv.symm (f.app ⟨X⟩ x) := by
  apply yonedaEquiv.injective
  simp [yonedaEquiv_comp]

lemma map_yonedaEquiv {X Y : C} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj X ⟶ F)
    (g : Y ⟶ X) : F.map g.op (yonedaEquiv f) = f.app (op Y) g := by
  rw [yonedaEquiv_naturality, yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma map_yonedaEquiv' {X Y : Cᵒᵖ} {F : Cᵒᵖ ⥤ Type v₁} (f : yoneda.obj (unop X) ⟶ F)
    (g : X ⟶ Y) : F.map g (yonedaEquiv f) = f.app Y g.unop := by
  rw [yonedaEquiv_naturality', yonedaEquiv_comp, yonedaEquiv_yoneda_map]

lemma yonedaEquiv_symm_map {X Y : Cᵒᵖ} (f : X ⟶ Y) {F : Cᵒᵖ ⥤ Type v₁} (t : F.obj X) :
    yonedaEquiv.symm (F.map f t) = yoneda.map f.unop ≫ yonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := yonedaEquiv.surjective t
  rw [yonedaEquiv_naturality', Equiv.symm_apply_apply, Equiv.symm_apply_apply]

lemma hom_ext_yoneda {P Q : Cᵒᵖ ⥤ Type v₁} {f g : P ⟶ Q}
    (h : ∀ (X : C) (p : yoneda.obj X ⟶ P), p ≫ f = p ≫ g) :
    f = g := by
  ext X x
  simpa only [yonedaEquiv_comp, Equiv.apply_symm_apply]
    using congr_arg (yonedaEquiv) (h _ (yonedaEquiv.symm x))

variable (C)

def yonedaEvaluation : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried Cᵒᵖ (Type v₁) ⋙ uliftFunctor

@[simp]
theorem yonedaEvaluation_map_down (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (yonedaEvaluation C).obj P) :
    ((yonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

def yonedaPairing : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod yoneda.op (𝟭 (Cᵒᵖ ⥤ Type v₁)) ⋙ Functor.hom (Cᵒᵖ ⥤ Type v₁)

@[ext]
lemma yonedaPairingExt {X : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)} {x y : (yonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem yonedaPairing_map (P Q : Cᵒᵖ × (Cᵒᵖ ⥤ Type v₁)) (α : P ⟶ Q) (β : (yonedaPairing C).obj P) :
    (yonedaPairing C).map α β = yoneda.map α.1.unop ≫ β ≫ α.2 :=
  rfl

universe w in
variable {C} in

def yonedaCompUliftFunctorEquiv (F : Cᵒᵖ ⥤ Type max v₁ w) (X : C) :
    (yoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj (op X) where
  toFun φ := φ.app (op X) (ULift.up (𝟙 _))
  invFun f :=
    { app := fun _ x => F.map (ULift.down x).op f }
  left_inv φ := by
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    dsimp
    rw [Category.comp_id]
    rfl
  right_inv f := by aesop_cat

def yonedaLemma : yonedaPairing C ≅ yonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (yonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : yoneda.obj X.unop ⟶ F)
        apply ULift.ext
        simp only [Functor.prod_obj, Functor.id_obj, types_comp_apply, yonedaEvaluation_map_down]
        erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
        dsimp [yonedaEquiv]
        simp [← FunctorToTypes.naturality])

variable {C}

def curriedYonedaLemma {C : Type u₁} [SmallCategory C] :
    (yoneda.op ⋙ coyoneda : Cᵒᵖ ⥤ (Cᵒᵖ ⥤ Type u₁) ⥤ Type u₁) ≅ evaluation Cᵒᵖ (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv)) (by
    intro X Y f
    ext a b
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality])

def largeCurriedYonedaLemma {C : Type u₁} [Category.{v₁} C] :
    yoneda.op ⋙ coyoneda ≅
      evaluation Cᵒᵖ (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| yonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using yonedaEquiv_comp _ _))
    (by
      intros Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (yonedaEquiv_naturality _ _).symm)

def yonedaOpCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : Cᵒᵖ ⥤ Type v₁) :
    yoneda.op ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedYonedaLemma ((evaluation _ _).obj P)

def curriedYonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft Cᵒᵖ (Cᵒᵖ ⥤ Type u₁)ᵒᵖ (Type u₁)).obj yoneda.op
      ≅ 𝟭 (Cᵒᵖ ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso yonedaEquiv) (by
    intro X Y f
    ext a
    dsimp [yonedaEquiv]
    simp [← FunctorToTypes.naturality]))

lemma isIso_of_yoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) :
    IsIso f := by
  obtain ⟨g, hg : g ≫ f = 𝟙 Y⟩ := (hf Y).2 (𝟙 Y)
  exact ⟨g, (hf _).1 (by aesop_cat), hg⟩

lemma isIso_iff_yoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : T ⟶ X) => x ≫ f)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_yoneda_map_bijective f hf⟩
  have : IsIso (yoneda.map f) := inferInstance
  intro T
  rw [← isIso_iff_bijective]
  exact inferInstanceAs (IsIso ((yoneda.map f).app _))

lemma isIso_iff_isIso_yoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((yoneda.map f).app ⟨c⟩) := by
  rw [isIso_iff_yoneda_map_bijective]
  exact forall_congr' fun _ ↦ (isIso_iff_bijective _).symm

end YonedaLemma

section CoyonedaLemma

variable {C}

def coyonedaEquiv {X : C} {F : C ⥤ Type v₁} : (coyoneda.obj (op X) ⟶ F) ≃ F.obj X where
  toFun η := η.app X (𝟙 X)
  invFun ξ := { app := fun _ x ↦ F.map x ξ }
  left_inv := fun η ↦ by
    ext Y (x : X ⟶ Y)
    dsimp
    rw [← FunctorToTypes.naturality]
    simp
  right_inv := by intro ξ; simp

theorem coyonedaEquiv_apply {X : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F) :
    coyonedaEquiv f = f.app X (𝟙 X) :=
  rfl

@[simp]
theorem coyonedaEquiv_symm_app_apply {X : C} {F : C ⥤ Type v₁} (x : F.obj X) (Y : C)
    (f : X ⟶ Y) : (coyonedaEquiv.symm x).app Y f = F.map f x :=
  rfl

lemma coyonedaEquiv_naturality {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = coyonedaEquiv (coyoneda.map g.op ≫ f) := by
  change (f.app X ≫ F.map g) (𝟙 X) = f.app Y (g ≫ 𝟙 Y)
  rw [← f.naturality]
  dsimp
  simp

lemma coyonedaEquiv_comp {X : C} {F G : C ⥤ Type v₁} (α : coyoneda.obj (op X) ⟶ F) (β : F ⟶ G) :
    coyonedaEquiv (α ≫ β) = β.app _ (coyonedaEquiv α) := by
  rfl

lemma coyonedaEquiv_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    coyonedaEquiv (coyoneda.map f.op) = f := by
  rw [coyonedaEquiv_apply]
  simp

lemma map_coyonedaEquiv {X Y : C} {F : C ⥤ Type v₁} (f : coyoneda.obj (op X) ⟶ F)
    (g : X ⟶ Y) : F.map g (coyonedaEquiv f) = f.app Y g := by
  rw [coyonedaEquiv_naturality, coyonedaEquiv_comp, coyonedaEquiv_coyoneda_map]

lemma coyonedaEquiv_symm_map {X Y : C} (f : X ⟶ Y) {F : C ⥤ Type v₁} (t : F.obj X) :
    coyonedaEquiv.symm (F.map f t) = coyoneda.map f.op ≫ coyonedaEquiv.symm t := by
  obtain ⟨u, rfl⟩ := coyonedaEquiv.surjective t
  simp [coyonedaEquiv_naturality u f]

variable (C)

def coyonedaEvaluation : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  evaluationUncurried C (Type v₁) ⋙ uliftFunctor

@[simp]
theorem coyonedaEvaluation_map_down (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q)
    (x : (coyonedaEvaluation C).obj P) :
    ((coyonedaEvaluation C).map α x).down = α.2.app Q.1 (P.2.map α.1 x.down) :=
  rfl

def coyonedaPairing : C × (C ⥤ Type v₁) ⥤ Type max u₁ v₁ :=
  Functor.prod coyoneda.rightOp (𝟭 (C ⥤ Type v₁)) ⋙ Functor.hom (C ⥤ Type v₁)

@[ext]
lemma coyonedaPairingExt {X : C × (C ⥤ Type v₁)} {x y : (coyonedaPairing C).obj X}
    (w : ∀ Y, x.app Y = y.app Y) : x = y :=
  NatTrans.ext (funext w)

@[simp]
theorem coyonedaPairing_map (P Q : C × (C ⥤ Type v₁)) (α : P ⟶ Q) (β : (coyonedaPairing C).obj P) :
    (coyonedaPairing C).map α β = coyoneda.map α.1.op ≫ β ≫ α.2 :=
  rfl

universe w in
variable {C} in

def coyonedaCompUliftFunctorEquiv (F : C ⥤ Type max v₁ w) (X : Cᵒᵖ) :
    (coyoneda.obj X ⋙ uliftFunctor ⟶ F) ≃ F.obj X.unop where
  toFun φ := φ.app X.unop (ULift.up (𝟙 _))
  invFun f :=
    { app := fun _ x => F.map (ULift.down x) f }
  left_inv φ := by
    ext Y f
    dsimp
    rw [← FunctorToTypes.naturality]
    dsimp
    rw [Category.id_comp]
    rfl
  right_inv f := by aesop_cat

def coyonedaLemma : coyonedaPairing C ≅ coyonedaEvaluation C :=
  NatIso.ofComponents
    (fun _ ↦ Equiv.toIso (coyonedaEquiv.trans Equiv.ulift.symm))
    (by intro (X, F) (Y, G) f
        ext (a : coyoneda.obj (op X) ⟶ F)
        apply ULift.ext
        simp only [Functor.prod_obj, Functor.id_obj, types_comp_apply, coyonedaEvaluation_map_down]
        erw [Equiv.ulift_symm_down, Equiv.ulift_symm_down]
        simp [coyonedaEquiv, ← FunctorToTypes.naturality])

variable {C}

def curriedCoyonedaLemma {C : Type u₁} [SmallCategory C] :
    coyoneda.rightOp ⋙ coyoneda ≅ evaluation C (Type u₁) :=
  NatIso.ofComponents (fun X ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv)) (by
    intro X Y f
    ext a b
    simp [coyonedaEquiv, ← FunctorToTypes.naturality])

def largeCurriedCoyonedaLemma {C : Type u₁} [Category.{v₁} C] :
    (coyoneda.rightOp ⋙ coyoneda) ≅
      evaluation C (Type v₁) ⋙ (whiskeringRight _ _ _).obj uliftFunctor.{u₁} :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents
      (fun _ => Equiv.toIso <| coyonedaEquiv.trans Equiv.ulift.symm)
      (by
        intros Y Z f
        ext g
        rw [← ULift.down_inj]
        simpa using coyonedaEquiv_comp _ _))
    (by
      intro Y Z f
      ext F g
      rw [← ULift.down_inj]
      simpa using (coyonedaEquiv_naturality _ _).symm)

def coyonedaCompYonedaObj {C : Type u₁} [Category.{v₁} C] (P : C ⥤ Type v₁) :
    coyoneda.rightOp ⋙ yoneda.obj P ≅ P ⋙ uliftFunctor.{u₁} :=
  isoWhiskerRight largeCurriedCoyonedaLemma ((evaluation _ _).obj P)

def curriedCoyonedaLemma' {C : Type u₁} [SmallCategory C] :
    yoneda ⋙ (whiskeringLeft C (C ⥤ Type u₁)ᵒᵖ (Type u₁)).obj coyoneda.rightOp
      ≅ 𝟭 (C ⥤ Type u₁) :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents (fun _ ↦ Equiv.toIso coyonedaEquiv) (by
    intro X Y f
    ext a
    simp [coyonedaEquiv, ← FunctorToTypes.naturality]))

lemma isIso_of_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y)
    (hf : ∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) :
    IsIso f := by
  obtain ⟨g, hg : f ≫ g = 𝟙 X⟩ := (hf X).2 (𝟙 X)
  refine ⟨g, hg, (hf _).1 ?_⟩
  simp only [Category.comp_id, ← Category.assoc, hg, Category.id_comp]

lemma isIso_iff_coyoneda_map_bijective {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ (∀ (T : C), Function.Bijective (fun (x : Y ⟶ T) => f ≫ x)) := by
  refine ⟨fun _ ↦ ?_, fun hf ↦ isIso_of_coyoneda_map_bijective f hf⟩
  have : IsIso (coyoneda.map f.op) := inferInstance
  intro T
  rw [← isIso_iff_bijective]
  exact inferInstanceAs (IsIso ((coyoneda.map f.op).app _))

lemma isIso_iff_isIso_coyoneda_map {X Y : C} (f : X ⟶ Y) :
    IsIso f ↔ ∀ c : C, IsIso ((coyoneda.map f.op).app c) := by
  rw [isIso_iff_coyoneda_map_bijective]
  exact forall_congr' fun _ ↦ (isIso_iff_bijective _).symm

end CoyonedaLemma

section

variable {C}

variable {D : Type*} [Category.{v₁} D] (F : C ⥤ D)

def yonedaMap (X : C) : yoneda.obj X ⟶ F.op ⋙ yoneda.obj (F.obj X) where
  app _ f := F.map f

@[simp]
lemma yonedaMap_app_apply {Y : C} {X : Cᵒᵖ} (f : X.unop ⟶ Y) :
    (yonedaMap F Y).app X f = F.map f := rfl

end

namespace Functor.FullyFaithful

variable {C : Type u₁} [Category.{v₁} C]

@[simps!]
def homNatIso {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful) (X : C) :
    F.op ⋙ yoneda.obj (F.obj X) ⋙ uliftFunctor.{v₁} ≅ yoneda.obj X ⋙ uliftFunctor.{v₂} :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (Equiv.ulift.trans <| hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

@[simps!]
def homNatIsoMaxRight {D : Type u₂} [Category.{max v₁ v₂} D] {F : C ⥤ D} (hF : F.FullyFaithful)
    (X : C) : F.op ⋙ yoneda.obj (F.obj X) ≅ yoneda.obj X ⋙ uliftFunctor.{v₂} :=
  NatIso.ofComponents
    (fun Y => Equiv.toIso (hF.homEquiv.symm.trans Equiv.ulift.symm))
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

@[simps!]
def compYonedaCompWhiskeringLeft {D : Type u₂} [Category.{v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) : F ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ⋙
      (CategoryTheory.whiskeringRight _ _ _).obj uliftFunctor.{v₁} ≅
      yoneda ⋙ (CategoryTheory.whiskeringRight _ _ _).obj uliftFunctor.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIso _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

@[simps!]
def compYonedaCompWhiskeringLeftMaxRight {D : Type u₂} [Category.{max v₁ v₂} D] {F : C ⥤ D}
    (hF : F.FullyFaithful) : F ⋙ yoneda ⋙ (whiskeringLeft _ _ _).obj F.op ≅
      yoneda ⋙ (CategoryTheory.whiskeringRight _ _ _).obj uliftFunctor.{v₂} :=
  NatIso.ofComponents (fun X => hF.homNatIsoMaxRight _)
    (fun f => by ext; exact Equiv.ulift.injective (hF.map_injective (by simp)))

end Functor.FullyFaithful

end CategoryTheory
