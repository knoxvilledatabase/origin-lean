/-
Extracted from CategoryTheory/GradedObject/Bifunctor.lean
Genuine: 10 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.GradedObject

noncomputable section

/-!
# The action of bifunctors on graded objects

Given a bifunctor `F : C₁ ⥤ C₂ ⥤ C₃` and types `I` and `J`, we construct an obvious functor
`mapBifunctor F I J : GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃`.
When we have a map `p : I × J → K` and that suitable coproducts exists, we also get
a functor
`mapBifunctorMap F p : GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃`.

In case `p : I × I → I` is the addition on a monoid and `F` is the tensor product on a monoidal
category `C`, these definitions shall be used in order to construct a monoidal structure
on `GradedObject I C` (TODO @joelriou).

-/

namespace CategoryTheory

open Category

variable {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
  (F : C₁ ⥤ C₂ ⥤ C₃)

namespace GradedObject

@[simps]
def mapBifunctor (I J : Type*) :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject (I × J) C₃ where
  obj X :=
    { obj := fun Y ij => (F.obj (X ij.1)).obj (Y ij.2)
      map := fun φ ij => (F.obj (X ij.1)).map (φ ij.2) }
  map φ :=
    { app := fun Y ij => (F.map (φ ij.1)).app (Y ij.2) }

section

variable {I J K : Type*} (p : I × J → K)

noncomputable def mapBifunctorMapObj (X : GradedObject I C₁) (Y : GradedObject J C₂)
  [HasMap (((mapBifunctor F I J).obj X).obj Y) p] : GradedObject K C₃ :=
    (((mapBifunctor F I J).obj X).obj Y).mapObj p

noncomputable def ιMapBifunctorMapObj
    (X : GradedObject I C₁) (Y : GradedObject J C₂)
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (i : I) (j : J) (k : K) (h : p ⟨i, j⟩ = k) :
    (F.obj (X i)).obj (Y j) ⟶ mapBifunctorMapObj F p X Y k :=
  (((mapBifunctor F I J).obj X).obj Y).ιMapObj p ⟨i, j⟩ k h

noncomputable def mapBifunctorMapMap {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y₂)
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p] :
    mapBifunctorMapObj F p X₁ Y₁ ⟶ mapBifunctorMapObj F p X₂ Y₂ :=
  GradedObject.mapMap (((mapBifunctor F I J).map f).app Y₁ ≫
    ((mapBifunctor F I J).obj X₂).map g) p

@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapMap {X₁ X₂ : GradedObject I C₁} (f : X₁ ⟶ X₂)
    {Y₁ Y₂ : GradedObject J C₂} (g : Y₁ ⟶ Y₂)
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p]
    (i : I) (j : J) (k : K) (h : p ⟨i, j⟩ = k) :
    ιMapBifunctorMapObj F p X₁ Y₁ i j k h ≫ mapBifunctorMapMap F p f g k =
      (F.map (f i)).app (Y₁ j) ≫ (F.obj (X₂ i)).map (g j) ≫
        ιMapBifunctorMapObj F p X₂ Y₂ i j k h := by
  simp [ιMapBifunctorMapObj, mapBifunctorMapMap]

@[ext]
lemma mapBifunctorMapObj_ext {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    {f g : mapBifunctorMapObj F p X Y k ⟶ A}
    (h : ∀ (i : I) (j : J) (hij : p ⟨i, j⟩ = k),
      ιMapBifunctorMapObj F p X Y i j k hij ≫ f = ιMapBifunctorMapObj F p X Y i j k hij ≫ g) :
    f = g := by
  apply mapObj_ext
  rintro ⟨i, j⟩ hij
  exact h i j hij

variable {F p} in

noncomputable def mapBifunctorMapObjDesc
    {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (f : ∀ (i : I) (j : J) (_ : p ⟨i, j⟩ = k), (F.obj (X i)).obj (Y j) ⟶ A) :
    mapBifunctorMapObj F p X Y k ⟶ A :=
  descMapObj _ _ (fun ⟨i, j⟩ hij => f i j hij)

@[reassoc (attr := simp)]
lemma ι_mapBifunctorMapObjDesc {X : GradedObject I C₁} {Y : GradedObject J C₂} {A : C₃} {k : K}
    [HasMap (((mapBifunctor F I J).obj X).obj Y) p]
    (f : ∀ (i : I) (j : J) (_ : p ⟨i, j⟩ = k), (F.obj (X i)).obj (Y j) ⟶ A)
    (i : I) (j : J) (hij : p ⟨i, j⟩ = k) :
    ιMapBifunctorMapObj F p X Y i j k hij ≫ mapBifunctorMapObjDesc f = f i j hij := by
  apply ι_descMapObj

section

variable {X₁ X₂ : GradedObject I C₁} {Y₁ Y₂ : GradedObject J C₂}
    [HasMap (((mapBifunctor F I J).obj X₁).obj Y₁) p]
    [HasMap (((mapBifunctor F I J).obj X₂).obj Y₂) p]

@[simps]
noncomputable def mapBifunctorMapMapIso (e : X₁ ≅ X₂) (e' : Y₁ ≅ Y₂) :
    mapBifunctorMapObj F p X₁ Y₁ ≅ mapBifunctorMapObj F p X₂ Y₂ where
  hom := mapBifunctorMapMap F p e.hom e'.hom
  inv := mapBifunctorMapMap F p e.inv e'.inv
  hom_inv_id := by ext; simp
  inv_hom_id := by ext; simp

instance (f : X₁ ⟶ X₂) (g : Y₁ ⟶ Y₂) [IsIso f] [IsIso g] :
    IsIso (mapBifunctorMapMap F p f g) :=
  (inferInstance : IsIso (mapBifunctorMapMapIso F p (asIso f) (asIso g)).hom)

end

attribute [local simp] mapBifunctorMapMap

@[simps]
noncomputable def mapBifunctorMap [∀ X Y, HasMap (((mapBifunctor F I J).obj X).obj Y) p] :
    GradedObject I C₁ ⥤ GradedObject J C₂ ⥤ GradedObject K C₃ where
  obj X :=
    { obj := fun Y => mapBifunctorMapObj F p X Y
      map := fun ψ => mapBifunctorMapMap F p (𝟙 X) ψ }
  map {X₁ X₂} φ :=
    { app := fun Y => mapBifunctorMapMap F p φ (𝟙 Y)
      naturality := fun {Y₁ Y₂} ψ => by
        dsimp
        simp only [Functor.map_id, NatTrans.id_app, id_comp, comp_id,
          ← mapMap_comp, NatTrans.naturality] }

end

end GradedObject

end CategoryTheory
