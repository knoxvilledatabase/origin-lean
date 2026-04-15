/-
Extracted from AlgebraicTopology/FundamentalGroupoid/Product.lean
Genuine: 10 of 16 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core
import Mathlib.CategoryTheory.Groupoid
import Mathlib.AlgebraicTopology.FundamentalGroupoid.Basic
import Mathlib.Topology.Category.TopCat.Limits.Products
import Mathlib.Topology.Homotopy.Product

/-!
# Fundamental groupoid preserves products
In this file, we give the following definitions/theorems:

  - `FundamentalGroupoidFunctor.piIso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `FundamentalGroupoidFunctor.prodIso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `FundamentalGroupoidFunctor.preservesProduct` A proof that the fundamental groupoid functor
    preserves all products.
-/

noncomputable section

open scoped FundamentalGroupoid CategoryTheory

namespace FundamentalGroupoidFunctor

universe u

section Pi

variable {I : Type u} (X : I → TopCat.{u})

def proj (i : I) : πₓ (TopCat.of (∀ i, X i)) ⥤ πₓ (X i) :=
  πₘ ⟨_, continuous_apply i⟩

@[simp]
theorem proj_map (i : I) (x₀ x₁ : πₓ (TopCat.of (∀ i, X i))) (p : x₀ ⟶ x₁) :
    (proj X i).map p = @Path.Homotopic.proj _ _ _ _ _ i p :=
  rfl

@[simps]
def piToPiTop : (∀ i, πₓ (X i)) ⥤ πₓ (TopCat.of (∀ i, X i)) where
  obj g := ⟨fun i => (g i).as⟩
  map p := Path.Homotopic.pi p
  map_id x := by
    change (Path.Homotopic.pi fun i => ⟦_⟧) = _
    simp only [FundamentalGroupoid.id_eq_path_refl, Path.Homotopic.pi_lift]
    rfl
  map_comp f g := (Path.Homotopic.comp_pi_eq_pi_comp f g).symm

@[simps]
def piIso : CategoryTheory.Grpd.of (∀ i : I, πₓ (X i)) ≅ πₓ (TopCat.of (∀ i, X i)) where
  hom := piToPiTop X
  inv := CategoryTheory.Functor.pi' (proj X)
  hom_inv_id := by
    change piToPiTop X ⋙ CategoryTheory.Functor.pi' (proj X) = 𝟭 _
    apply CategoryTheory.Functor.ext ?_ ?_
    · intros; rfl
    · intros; ext; simp
  inv_hom_id := by
    change CategoryTheory.Functor.pi' (proj X) ⋙ piToPiTop X = 𝟭 _
    apply CategoryTheory.Functor.ext
    · intro _ _ f
      suffices Path.Homotopic.pi ((CategoryTheory.Functor.pi' (proj X)).map f) = f by simpa
      change Path.Homotopic.pi (fun i => (CategoryTheory.Functor.pi' (proj X)).map f i) = _
      simp
    · intros; rfl

section Preserves

open CategoryTheory

def coneDiscreteComp :
    Limits.Cone (Discrete.functor X ⋙ π) ≌ Limits.Cone (Discrete.functor fun i => πₓ (X i)) :=
  Limits.Cones.postcomposeEquivalence (Discrete.compNatIsoDiscrete X π)

theorem coneDiscreteComp_obj_mapCone :
    -- Porting note: check universe parameters here
    (coneDiscreteComp X).functor.obj (Functor.mapCone π (TopCat.piFan.{u,u} X)) =
      Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) :=
  rfl

def piTopToPiCone :
    Limits.Fan.mk (πₓ (TopCat.of (∀ i, X i))) (proj X) ⟶ Grpd.piLimitFan fun i : I => πₓ (X i) where
  hom := CategoryTheory.Functor.pi' (proj X)

instance : IsIso (piTopToPiCone X) :=
  haveI : IsIso (piTopToPiCone X).hom := (inferInstance : IsIso (piIso X).inv)
  Limits.Cones.cone_iso_of_hom_iso (piTopToPiCone X)

lemma preservesProduct : Limits.PreservesLimit (Discrete.functor X) π := by
  -- Porting note: check universe parameters here
  apply Limits.preservesLimit_of_preserves_limit_cone (TopCat.piFanIsLimit.{u,u} X)
  apply (Limits.IsLimit.ofConeEquiv (coneDiscreteComp X)).toFun
  simp only [coneDiscreteComp_obj_mapCone]
  apply Limits.IsLimit.ofIsoLimit _ (asIso (piTopToPiCone X)).symm
  exact Grpd.piLimitFanIsLimit _

end Preserves

end Pi

section Prod

variable (A B : TopCat.{u})

def projLeft : πₓ (TopCat.of (A × B)) ⥤ πₓ A :=
  πₘ ⟨_, continuous_fst⟩

def projRight : πₓ (TopCat.of (A × B)) ⥤ πₓ B :=
  πₘ ⟨_, continuous_snd⟩

@[simp]
theorem projLeft_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projLeft A B).map p = Path.Homotopic.projLeft p :=
  rfl

@[simp]
theorem projRight_map (x₀ x₁ : πₓ (TopCat.of (A × B))) (p : x₀ ⟶ x₁) :
    (projRight A B).map p = Path.Homotopic.projRight p :=
  rfl

@[simps obj]
def prodToProdTop : πₓ A × πₓ B ⥤ πₓ (TopCat.of (A × B)) where
  obj g := ⟨g.fst.as, g.snd.as⟩
  map {x y} p :=
    match x, y, p with
    | (_, _), (_, _), (p₀, p₁) => @Path.Homotopic.prod _ _ (_) (_) _ _ _ _ p₀ p₁
  map_id := by
    rintro ⟨x₀, x₁⟩
    simp only [CategoryTheory.prod_id, FundamentalGroupoid.id_eq_path_refl]
    rfl
  map_comp {x y z} f g :=
    match x, y, z, f, g with
    | (_, _), (_, _), (_, _), (f₀, f₁), (g₀, g₁) =>
      (Path.Homotopic.comp_prod_eq_prod_comp f₀ f₁ g₀ g₁).symm

theorem prodToProdTop_map {x₀ x₁ : πₓ A} {y₀ y₁ : πₓ B} (p₀ : x₀ ⟶ x₁) (p₁ : y₀ ⟶ y₁) :
    (prodToProdTop A B).map (X := (x₀, y₀)) (Y := (x₁, y₁)) (p₀, p₁) =
      Path.Homotopic.prod p₀ p₁ :=
  rfl

@[simps]
def prodIso : CategoryTheory.Grpd.of (πₓ A × πₓ B) ≅ πₓ (TopCat.of (A × B)) where
  hom := prodToProdTop A B
  inv := (projLeft A B).prod' (projRight A B)
  hom_inv_id := by
    change prodToProdTop A B ⋙ (projLeft A B).prod' (projRight A B) = 𝟭 _
    apply CategoryTheory.Functor.hext; · intros; ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ ⟨f₀, f₁⟩
    have : Path.Homotopic.projLeft ((prodToProdTop A B).map (f₀, f₁)) = f₀ ∧
      Path.Homotopic.projRight ((prodToProdTop A B).map (f₀, f₁)) = f₁ :=
        And.intro (Path.Homotopic.projLeft_prod f₀ f₁) (Path.Homotopic.projRight_prod f₀ f₁)
    simpa
  inv_hom_id := by
    change (projLeft A B).prod' (projRight A B) ⋙ prodToProdTop A B = 𝟭 _
    apply CategoryTheory.Functor.hext
    · intros; apply FundamentalGroupoid.ext; apply Prod.ext <;> simp <;> rfl
    rintro ⟨x₀, x₁⟩ ⟨y₀, y₁⟩ f
    have := Path.Homotopic.prod_projLeft_projRight f
    -- Porting note: was simpa but TopSpace instances might be getting in the way
    simp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.prod'_obj, prodToProdTop_obj,
      CategoryTheory.Functor.comp_map, CategoryTheory.Functor.prod'_map, projLeft_map,
      projRight_map, CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map, heq_eq_eq]
    apply this

end Prod

end FundamentalGroupoidFunctor
