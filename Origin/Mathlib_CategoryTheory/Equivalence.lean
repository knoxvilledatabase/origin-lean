/-
Extracted from CategoryTheory/Equivalence.lean
Genuine: 59 | Conflates: 0 | Dissolved: 0 | Infrastructure: 25
-/
import Origin.Core
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.FullSubcategory
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EssentialImage
import Mathlib.Tactic.CategoryTheory.Slice

/-!
# Equivalence of categories

An equivalence of categories `C` and `D` is a pair of functors `F : C ⥤ D` and `G : D ⥤ C` such
that `η : 𝟭 C ≅ F ⋙ G` and `ε : G ⋙ F ≅ 𝟭 D`. In many situations, equivalences are a better
notion of "sameness" of categories than the stricter isomorphism of categories.

Recall that one way to express that two functors `F : C ⥤ D` and `G : D ⥤ C` are adjoint is using
two natural transformations `η : 𝟭 C ⟶ F ⋙ G` and `ε : G ⋙ F ⟶ 𝟭 D`, called the unit and the
counit, such that the compositions `F ⟶ FGF ⟶ F` and `G ⟶ GFG ⟶ G` are the identity. Unfortunately,
it is not the case that the natural isomorphisms `η` and `ε` in the definition of an equivalence
automatically give an adjunction. However, it is true that
* if one of the two compositions is the identity, then so is the other, and
* given an equivalence of categories, it is always possible to refine `η` in such a way that the
  identities are satisfied.

For this reason, in mathlib we define an equivalence to be a "half-adjoint equivalence", which is
a tuple `(F, G, η, ε)` as in the first paragraph such that the composite `F ⟶ FGF ⟶ F` is the
identity. By the remark above, this already implies that the tuple is an "adjoint equivalence",
i.e., that the composite `G ⟶ GFG ⟶ G` is also the identity.

We also define essentially surjective functors and show that a functor is an equivalence if and only
if it is full, faithful and essentially surjective.

## Main definitions

* `Equivalence`: bundled (half-)adjoint equivalences of categories
* `Functor.EssSurj`: type class on a functor `F` containing the data of the preimages
  and the isomorphisms `F.obj (preimage d) ≅ d`.
* `Functor.IsEquivalence`: type class on a functor `F` which is full, faithful and
essentially surjective.

## Main results

* `Equivalence.mk`: upgrade an equivalence to a (half-)adjoint equivalence
* `isEquivalence_iff_of_iso`: when `F` and `G` are isomorphic functors,
`F` is an equivalence iff `G` is.
* `Functor.asEquivalenceFunctor`: construction of an equivalence of categories from
a functor `F` which satisfies the property `F.IsEquivalence` (i.e. `F` is full, faithful
and essentially surjective).

## Notations

We write `C ≌ D` (`\backcong`, not to be confused with `≅`/`\cong`) for a bundled equivalence.

-/

namespace CategoryTheory

open CategoryTheory.Functor NatIso Category

universe v₁ v₂ v₃ u₁ u₂ u₃

@[ext]
structure Equivalence (C : Type u₁) (D : Type u₂) [Category.{v₁} C] [Category.{v₂} D] where mk' ::
  /-- A functor in one direction -/
  functor : C ⥤ D
  /-- A functor in the other direction -/
  inverse : D ⥤ C
  /-- The composition `functor ⋙ inverse` is isomorphic to the identity -/
  unitIso : 𝟭 C ≅ functor ⋙ inverse
  /-- The composition `inverse ⋙ functor` is also isomorphic to the identity -/
  counitIso : inverse ⋙ functor ≅ 𝟭 D
  /-- The natural isomorphisms compose to the identity. -/
  functor_unitIso_comp :
    ∀ X : C, functor.map (unitIso.hom.app X) ≫ counitIso.hom.app (functor.obj X) =
      𝟙 (functor.obj X) := by aesop_cat

infixr:10 " ≌ " => Equivalence

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

abbrev unit (e : C ≌ D) : 𝟭 C ⟶ e.functor ⋙ e.inverse :=
  e.unitIso.hom

abbrev counit (e : C ≌ D) : e.inverse ⋙ e.functor ⟶ 𝟭 D :=
  e.counitIso.hom

abbrev unitInv (e : C ≌ D) : e.functor ⋙ e.inverse ⟶ 𝟭 C :=
  e.unitIso.inv

abbrev counitInv (e : C ≌ D) : 𝟭 D ⟶ e.inverse ⋙ e.functor :=
  e.counitIso.inv

@[simp]
theorem Equivalence_mk'_unit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unit = unit_iso.hom :=
  rfl

@[simp]
theorem Equivalence_mk'_counit (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counit = counit_iso.hom :=
  rfl

@[simp]
theorem Equivalence_mk'_unitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).unitInv = unit_iso.inv :=
  rfl

@[simp]
theorem Equivalence_mk'_counitInv (functor inverse unit_iso counit_iso f) :
    (⟨functor, inverse, unit_iso, counit_iso, f⟩ : C ≌ D).counitInv = counit_iso.inv :=
  rfl

@[reassoc (attr := simp)]
theorem functor_unit_comp (e : C ≌ D) (X : C) :
    e.functor.map (e.unit.app X) ≫ e.counit.app (e.functor.obj X) = 𝟙 (e.functor.obj X) :=
  e.functor_unitIso_comp X

@[reassoc (attr := simp)]
theorem counitInv_functor_comp (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) ≫ e.functor.map (e.unitInv.app X) = 𝟙 (e.functor.obj X) := by
  erw [Iso.inv_eq_inv (e.functor.mapIso (e.unitIso.app X) ≪≫ e.counitIso.app (e.functor.obj X))
      (Iso.refl _)]
  exact e.functor_unit_comp X

theorem counitInv_app_functor (e : C ≌ D) (X : C) :
    e.counitInv.app (e.functor.obj X) = e.functor.map (e.unit.app X) := by
  symm
  erw [← Iso.comp_hom_eq_id (e.counitIso.app _), functor_unit_comp]
  rfl

theorem counit_app_functor (e : C ≌ D) (X : C) :
    e.counit.app (e.functor.obj X) = e.functor.map (e.unitInv.app X) := by
  erw [← Iso.hom_comp_eq_id (e.functor.mapIso (e.unitIso.app X)), functor_unit_comp]
  rfl

@[reassoc (attr := simp)]
theorem unit_inverse_comp (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) ≫ e.inverse.map (e.counit.app Y) = 𝟙 (e.inverse.obj Y) := by
  rw [← id_comp (e.inverse.map _), ← map_id e.inverse, ← counitInv_functor_comp, map_comp]
  dsimp
  rw [← Iso.hom_inv_id_assoc (e.unitIso.app _) (e.inverse.map (e.functor.map _)), app_hom, app_inv]
  slice_lhs 2 3 => erw [e.unit.naturality]
  slice_lhs 1 2 => erw [e.unit.naturality]
  slice_lhs 4 4 =>
    rw [← Iso.hom_inv_id_assoc (e.inverse.mapIso (e.counitIso.app _)) (e.unitInv.app _)]
  slice_lhs 3 4 =>
    erw [← map_comp e.inverse, e.counit.naturality]
    erw [(e.counitIso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 2 3 => erw [← map_comp e.inverse, e.counitIso.inv.naturality, map_comp]
  slice_lhs 3 4 => erw [e.unitInv.naturality]
  slice_lhs 4 5 => erw [← map_comp (e.functor ⋙ e.inverse), (e.unitIso.app _).hom_inv_id, map_id]
  erw [id_comp]
  slice_lhs 3 4 => erw [← e.unitInv.naturality]
  slice_lhs 2 3 =>
    erw [← map_comp e.inverse, ← e.counitIso.inv.naturality, (e.counitIso.app _).hom_inv_id,
      map_id]
  erw [id_comp, (e.unitIso.app _).hom_inv_id]; rfl

@[reassoc (attr := simp)]
theorem inverse_counitInv_comp (e : C ≌ D) (Y : D) :
    e.inverse.map (e.counitInv.app Y) ≫ e.unitInv.app (e.inverse.obj Y) = 𝟙 (e.inverse.obj Y) := by
  erw [Iso.inv_eq_inv (e.unitIso.app (e.inverse.obj Y) ≪≫ e.inverse.mapIso (e.counitIso.app Y))
      (Iso.refl _)]
  exact e.unit_inverse_comp Y

theorem unit_app_inverse (e : C ≌ D) (Y : D) :
    e.unit.app (e.inverse.obj Y) = e.inverse.map (e.counitInv.app Y) := by
  erw [← Iso.comp_hom_eq_id (e.inverse.mapIso (e.counitIso.app Y)), unit_inverse_comp]
  dsimp

theorem unitInv_app_inverse (e : C ≌ D) (Y : D) :
    e.unitInv.app (e.inverse.obj Y) = e.inverse.map (e.counit.app Y) := by
  symm
  erw [← Iso.hom_comp_eq_id (e.unitIso.app _), unit_inverse_comp]
  rfl

@[reassoc, simp]
theorem fun_inv_map (e : C ≌ D) (X Y : D) (f : X ⟶ Y) :
    e.functor.map (e.inverse.map f) = e.counit.app X ≫ f ≫ e.counitInv.app Y :=
  (NatIso.naturality_2 e.counitIso f).symm

@[reassoc, simp]
theorem inv_fun_map (e : C ≌ D) (X Y : C) (f : X ⟶ Y) :
    e.inverse.map (e.functor.map f) = e.unitInv.app X ≫ f ≫ e.unit.app Y :=
  (NatIso.naturality_1 e.unitIso f).symm

section

variable {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D)

def adjointifyη : 𝟭 C ≅ F ⋙ G := by
  calc
    𝟭 C ≅ F ⋙ G := η
    _ ≅ F ⋙ 𝟭 D ⋙ G := isoWhiskerLeft F (leftUnitor G).symm
    _ ≅ F ⋙ (G ⋙ F) ⋙ G := isoWhiskerLeft F (isoWhiskerRight ε.symm G)
    _ ≅ F ⋙ G ⋙ F ⋙ G := isoWhiskerLeft F (associator G F G)
    _ ≅ (F ⋙ G) ⋙ F ⋙ G := (associator F G (F ⋙ G)).symm
    _ ≅ 𝟭 C ⋙ F ⋙ G := isoWhiskerRight η.symm (F ⋙ G)
    _ ≅ F ⋙ G := leftUnitor (F ⋙ G)

@[reassoc]
theorem adjointify_η_ε (X : C) :
    F.map ((adjointifyη η ε).hom.app X) ≫ ε.hom.app (F.obj X) = 𝟙 (F.obj X) := by
  dsimp [adjointifyη,Trans.trans]
  simp only [comp_id, assoc, map_comp]
  have := ε.hom.naturality (F.map (η.inv.app X)); dsimp at this; rw [this]; clear this
  rw [← assoc _ _ (F.map _)]
  have := ε.hom.naturality (ε.inv.app <| F.obj X); dsimp at this; rw [this]; clear this
  have := (ε.app <| F.obj X).hom_inv_id; dsimp at this; rw [this]; clear this
  rw [id_comp]; have := (F.mapIso <| η.app X).hom_inv_id; dsimp at this; rw [this]

end

protected def mk (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) : C ≌ D :=
  ⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩

@[refl, simps]
def refl : C ≌ C :=
  ⟨𝟭 C, 𝟭 C, Iso.refl _, Iso.refl _, fun _ => Category.id_comp _⟩

instance : Inhabited (C ≌ C) :=
  ⟨refl⟩

@[symm, simps]
def symm (e : C ≌ D) : D ≌ C :=
  ⟨e.inverse, e.functor, e.counitIso.symm, e.unitIso.symm, e.inverse_counitInv_comp⟩

variable {E : Type u₃} [Category.{v₃} E]

@[trans, simps]
def trans (e : C ≌ D) (f : D ≌ E) : C ≌ E where
  functor := e.functor ⋙ f.functor
  inverse := f.inverse ⋙ e.inverse
  unitIso := by
    refine Iso.trans e.unitIso ?_
    exact isoWhiskerLeft e.functor (isoWhiskerRight f.unitIso e.inverse)
  counitIso := by
    refine Iso.trans ?_ f.counitIso
    exact isoWhiskerLeft f.inverse (isoWhiskerRight e.counitIso f.functor)
  -- We wouldn't have needed to give this proof if we'd used `Equivalence.mk`,
  -- but we choose to avoid using that here, for the sake of good structure projection `simp`
  -- lemmas.
  functor_unitIso_comp X := by
    dsimp
    rw [← f.functor.map_comp_assoc, e.functor.map_comp, ← counitInv_app_functor, fun_inv_map,
      Iso.inv_hom_id_app_assoc, assoc, Iso.inv_hom_id_app, counit_app_functor, ← Functor.map_comp]
    erw [comp_id, Iso.hom_inv_id_app, Functor.map_id]

def funInvIdAssoc (e : C ≌ D) (F : C ⥤ E) : e.functor ⋙ e.inverse ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.unitIso.symm F ≪≫ F.leftUnitor

@[simp]
theorem funInvIdAssoc_hom_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).hom.app X = F.map (e.unitInv.app X) := by
  dsimp [funInvIdAssoc]
  aesop_cat

@[simp]
theorem funInvIdAssoc_inv_app (e : C ≌ D) (F : C ⥤ E) (X : C) :
    (funInvIdAssoc e F).inv.app X = F.map (e.unit.app X) := by
  dsimp [funInvIdAssoc]
  aesop_cat

def invFunIdAssoc (e : C ≌ D) (F : D ⥤ E) : e.inverse ⋙ e.functor ⋙ F ≅ F :=
  (Functor.associator _ _ _).symm ≪≫ isoWhiskerRight e.counitIso F ≪≫ F.leftUnitor

@[simp]
theorem invFunIdAssoc_hom_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).hom.app X = F.map (e.counit.app X) := by
  dsimp [invFunIdAssoc]
  aesop_cat

@[simp]
theorem invFunIdAssoc_inv_app (e : C ≌ D) (F : D ⥤ E) (X : D) :
    (invFunIdAssoc e F).inv.app X = F.map (e.counitInv.app X) := by
  dsimp [invFunIdAssoc]
  aesop_cat

@[simps! functor inverse unitIso counitIso]
def congrLeft (e : C ≌ D) : C ⥤ E ≌ D ⥤ E where
  functor := (whiskeringLeft _ _ _).obj e.inverse
  inverse := (whiskeringLeft _ _ _).obj e.functor
  unitIso := (NatIso.ofComponents fun F => (e.funInvIdAssoc F).symm)
  counitIso := (NatIso.ofComponents fun F => e.invFunIdAssoc F)
  functor_unitIso_comp F := by
    ext X
    dsimp
    simp only [funInvIdAssoc_inv_app, id_obj, comp_obj, invFunIdAssoc_hom_app,
      Functor.comp_map, ← F.map_comp, unit_inverse_comp, map_id]

@[simps! functor inverse unitIso counitIso]
def congrRight (e : C ≌ D) : E ⥤ C ≌ E ⥤ D where
  functor := (whiskeringRight _ _ _).obj e.functor
  inverse := (whiskeringRight _ _ _).obj e.inverse
  unitIso := NatIso.ofComponents
      fun F => F.rightUnitor.symm ≪≫ isoWhiskerLeft F e.unitIso ≪≫ Functor.associator _ _ _
  counitIso := NatIso.ofComponents
      fun F => Functor.associator _ _ _ ≪≫ isoWhiskerLeft F e.counitIso ≪≫ F.rightUnitor

section CancellationLemmas

variable (e : C ≌ D)

@[simp]
theorem cancel_unit_right {X Y : C} (f f' : X ⟶ Y) :
    f ≫ e.unit.app Y = f' ≫ e.unit.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_unitInv_right {X Y : C} (f f' : X ⟶ e.inverse.obj (e.functor.obj Y)) :
    f ≫ e.unitInv.app Y = f' ≫ e.unitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_counit_right {X Y : D} (f f' : X ⟶ e.functor.obj (e.inverse.obj Y)) :
    f ≫ e.counit.app Y = f' ≫ e.counit.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_counitInv_right {X Y : D} (f f' : X ⟶ Y) :
    f ≫ e.counitInv.app Y = f' ≫ e.counitInv.app Y ↔ f = f' := by simp only [cancel_mono]

@[simp]
theorem cancel_unit_right_assoc {W X X' Y : C} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X') (g' : X' ⟶ Y) :
    f ≫ g ≫ e.unit.app Y = f' ≫ g' ≫ e.unit.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_counitInv_right_assoc {W X X' Y : D} (f : W ⟶ X) (g : X ⟶ Y) (f' : W ⟶ X')
    (g' : X' ⟶ Y) : f ≫ g ≫ e.counitInv.app Y = f' ≫ g' ≫ e.counitInv.app Y ↔ f ≫ g = f' ≫ g' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_unit_right_assoc' {W X X' Y Y' Z : C} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.unit.app Z = f' ≫ g' ≫ h' ≫ e.unit.app Z ↔ f ≫ g ≫ h = f' ≫ g' ≫ h' := by
  simp only [← Category.assoc, cancel_mono]

@[simp]
theorem cancel_counitInv_right_assoc' {W X X' Y Y' Z : D} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z)
    (f' : W ⟶ X') (g' : X' ⟶ Y') (h' : Y' ⟶ Z) :
    f ≫ g ≫ h ≫ e.counitInv.app Z = f' ≫ g' ≫ h' ≫ e.counitInv.app Z ↔
    f ≫ g ≫ h = f' ≫ g' ≫ h' := by simp only [← Category.assoc, cancel_mono]

end CancellationLemmas

section

def powNat (e : C ≌ C) : ℕ → (C ≌ C)
  | 0 => Equivalence.refl
  | 1 => e
  | n + 2 => e.trans (powNat e (n + 1))

def pow (e : C ≌ C) : ℤ → (C ≌ C)
  | Int.ofNat n => e.powNat n
  | Int.negSucc n => e.symm.powNat (n + 1)

instance : Pow (C ≌ C) ℤ :=
  ⟨pow⟩

@[simp]
theorem pow_zero (e : C ≌ C) : e ^ (0 : ℤ) = Equivalence.refl :=
  rfl

@[simp]
theorem pow_one (e : C ≌ C) : e ^ (1 : ℤ) = e :=
  rfl

@[simp]
theorem pow_neg_one (e : C ≌ C) : e ^ (-1 : ℤ) = e.symm :=
  rfl

end

instance essSurj_functor (e : C ≌ E) : e.functor.EssSurj :=
  ⟨fun Y => ⟨e.inverse.obj Y, ⟨e.counitIso.app Y⟩⟩⟩

instance essSurj_inverse (e : C ≌ E) : e.inverse.EssSurj :=
  e.symm.essSurj_functor

def fullyFaithfulFunctor (e : C ≌ E) : e.functor.FullyFaithful where
  preimage {X Y} f := e.unitIso.hom.app X ≫ e.inverse.map f ≫ e.unitIso.inv.app Y

def fullyFaithfulInverse (e : C ≌ E) : e.inverse.FullyFaithful where
  preimage {X Y} f := e.counitIso.inv.app X ≫ e.functor.map f ≫ e.counitIso.hom.app Y

instance faithful_functor (e : C ≌ E) : e.functor.Faithful :=
  e.fullyFaithfulFunctor.faithful

instance faithful_inverse (e : C ≌ E) : e.inverse.Faithful :=
  e.fullyFaithfulInverse.faithful

instance full_functor (e : C ≌ E) : e.functor.Full :=
  e.fullyFaithfulFunctor.full

instance full_inverse (e : C ≌ E) : e.inverse.Full :=
  e.fullyFaithfulInverse.full

@[simps!]
def changeFunctor (e : C ≌ D) {G : C ⥤ D} (iso : e.functor ≅ G) : C ≌ D where
  functor := G
  inverse := e.inverse
  unitIso := e.unitIso ≪≫ isoWhiskerRight iso _
  counitIso := isoWhiskerLeft _ iso.symm ≪≫ e.counitIso

theorem changeFunctor_refl (e : C ≌ D) : e.changeFunctor (Iso.refl _) = e := by aesop_cat

theorem changeFunctor_trans (e : C ≌ D) {G G' : C ⥤ D} (iso₁ : e.functor ≅ G) (iso₂ : G ≅ G') :
    (e.changeFunctor iso₁).changeFunctor iso₂ = e.changeFunctor (iso₁ ≪≫ iso₂) := by aesop_cat

@[simps!]
def changeInverse (e : C ≌ D) {G : D ⥤ C} (iso : e.inverse ≅ G) : C ≌ D where
  functor := e.functor
  inverse := G
  unitIso := e.unitIso ≪≫ isoWhiskerLeft _ iso
  counitIso := isoWhiskerRight iso.symm _ ≪≫ e.counitIso
  functor_unitIso_comp X := by
    dsimp
    rw [← map_comp_assoc, assoc, iso.hom_inv_id_app, comp_id, functor_unit_comp]

end Equivalence

class Functor.IsEquivalence (F : C ⥤ D) : Prop where
  faithful : F.Faithful := by infer_instance
  full : F.Full := by infer_instance
  essSurj : F.EssSurj := by infer_instance

instance Equivalence.isEquivalence_functor (F : C ≌ D) : IsEquivalence F.functor where

instance Equivalence.isEquivalence_inverse (F : C ≌ D) : IsEquivalence F.inverse :=
  F.symm.isEquivalence_functor

namespace Functor

namespace IsEquivalence

attribute [instance] faithful full essSurj

protected lemma mk' {F : C ⥤ D} (G : D ⥤ C) (η : 𝟭 C ≅ F ⋙ G) (ε : G ⋙ F ≅ 𝟭 D) :
    IsEquivalence F :=
  inferInstanceAs (IsEquivalence (Equivalence.mk F G η ε).functor)

end IsEquivalence

noncomputable def inv (F : C ⥤ D) [F.IsEquivalence] : D ⥤ C where
  obj X := F.objPreimage X
  map {X Y} f := F.preimage ((F.objObjPreimageIso X).hom ≫ f ≫ (F.objObjPreimageIso Y).inv)
  map_id X := by apply F.map_injective; aesop_cat
  map_comp {X Y Z} f g := by apply F.map_injective; simp

@[simps functor]
noncomputable def asEquivalence (F : C ⥤ D) [F.IsEquivalence] : C ≌ D where
  functor := F
  inverse := F.inv
  unitIso := NatIso.ofComponents
    (fun X => (F.preimageIso <| F.objObjPreimageIso <| F.obj X).symm)
      (fun f => F.map_injective (by simp [inv]))
  counitIso := NatIso.ofComponents F.objObjPreimageIso (by simp [inv])

instance isEquivalence_refl : IsEquivalence (𝟭 C) :=
  Equivalence.refl.isEquivalence_functor

instance isEquivalence_inv (F : C ⥤ D) [IsEquivalence F] : IsEquivalence F.inv :=
  F.asEquivalence.symm.isEquivalence_functor

variable {E : Type u₃} [Category.{v₃} E]

instance isEquivalence_trans (F : C ⥤ D) (G : D ⥤ E) [IsEquivalence F] [IsEquivalence G] :
    IsEquivalence (F ⋙ G) where

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringLeft C D E).obj F) :=
  (inferInstance : IsEquivalence (Equivalence.congrLeft F.asEquivalence).inverse)

instance (F : C ⥤ D) [IsEquivalence F] : IsEquivalence ((whiskeringRight E C D).obj F) :=
  (inferInstance : IsEquivalence (Equivalence.congrRight F.asEquivalence).functor)

end Functor

namespace Functor

@[simp]
theorem fun_inv_map (F : C ⥤ D) [IsEquivalence F] (X Y : D) (f : X ⟶ Y) :
    F.map (F.inv.map f) = F.asEquivalence.counit.app X ≫ f ≫ F.asEquivalence.counitInv.app Y := by
  erw [NatIso.naturality_2]
  rfl

@[simp]
theorem inv_fun_map (F : C ⥤ D) [IsEquivalence F] (X Y : C) (f : X ⟶ Y) :
    F.inv.map (F.map f) = F.asEquivalence.unitInv.app X ≫ f ≫ F.asEquivalence.unit.app Y := by
  erw [NatIso.naturality_1]
  rfl

lemma isEquivalence_of_iso {F G : C ⥤ D} (e : F ≅ G) [F.IsEquivalence] : G.IsEquivalence :=
  ((asEquivalence F).changeFunctor e).isEquivalence_functor

lemma isEquivalence_iff_of_iso {F G : C ⥤ D} (e : F ≅ G) :
    F.IsEquivalence ↔ G.IsEquivalence :=
  ⟨fun _ => isEquivalence_of_iso e, fun _ => isEquivalence_of_iso e.symm⟩

lemma isEquivalence_of_comp_right {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence G] [IsEquivalence (F ⋙ G)] : IsEquivalence F := by
  rw [isEquivalence_iff_of_iso (F.rightUnitor.symm ≪≫ isoWhiskerLeft F (G.asEquivalence.unitIso))]
  exact ((F ⋙ G).asEquivalence.trans G.asEquivalence.symm).isEquivalence_functor

lemma isEquivalence_of_comp_left {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E)
    [IsEquivalence F] [IsEquivalence (F ⋙ G)] : IsEquivalence G := by
  rw [isEquivalence_iff_of_iso (G.leftUnitor.symm ≪≫
    isoWhiskerRight F.asEquivalence.counitIso.symm G)]
  exact (F.asEquivalence.symm.trans (F ⋙ G).asEquivalence).isEquivalence_functor

end Functor

namespace Equivalence

instance essSurjInducedFunctor {C' : Type*} (e : C' ≃ D) : (inducedFunctor e).EssSurj where
  mem_essImage Y := ⟨e.symm Y, by simpa using ⟨default⟩⟩

noncomputable instance inducedFunctorOfEquiv {C' : Type*} (e : C' ≃ D) :
    IsEquivalence (inducedFunctor e) where

noncomputable instance fullyFaithfulToEssImage (F : C ⥤ D) [F.Full] [F.Faithful] :
    IsEquivalence F.toEssImage where

end Equivalence

namespace Iso

variable {E : Type u₃} [Category.{v₃} E] {F : C ⥤ E} {G : C ⥤ D} {H : D ⥤ E}

@[simps!]
def compInverseIso {H : D ≌ E} (i : F ≅ G ⋙ H.functor) : F ⋙ H.inverse ≅ G :=
  isoWhiskerRight i H.inverse ≪≫
    associator G _ H.inverse ≪≫ isoWhiskerLeft G H.unitIso.symm ≪≫ G.rightUnitor

@[simps!]
def isoCompInverse {H : D ≌ E} (i : G ⋙ H.functor ≅ F) : G ≅ F ⋙ H.inverse :=
  G.rightUnitor.symm ≪≫ isoWhiskerLeft G H.unitIso ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight i H.inverse

@[simps!]
def inverseCompIso {G : C ≌ D} (i : F ≅ G.functor ⋙ H) : G.inverse ⋙ F ≅ H :=
  isoWhiskerLeft G.inverse i ≪≫ (associator _ _ _).symm ≪≫
    isoWhiskerRight G.counitIso H ≪≫ H.leftUnitor

@[simps!]
def isoInverseComp {G : C ≌ D} (i : G.functor ⋙ H ≅ F) : H ≅ G.inverse ⋙ F :=
  H.leftUnitor.symm ≪≫ isoWhiskerRight G.counitIso.symm H ≪≫ associator _ _ _
    ≪≫ isoWhiskerLeft G.inverse i

end Iso

alias IsEquivalence.ofIso_trans := Equivalence.changeFunctor_trans

alias IsEquivalence.ofIso_refl := Equivalence.changeFunctor_refl

alias IsEquivalence.equivOfIso := Functor.isEquivalence_iff_of_iso

alias IsEquivalence.cancelCompRight := Functor.isEquivalence_of_comp_right

alias IsEquivalence.cancelCompLeft := Functor.isEquivalence_of_comp_left

end CategoryTheory
