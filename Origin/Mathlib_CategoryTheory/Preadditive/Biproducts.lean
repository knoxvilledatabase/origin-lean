/-
Extracted from CategoryTheory/Preadditive/Biproducts.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Basic facts about biproducts in preadditive categories.

In (or between) preadditive categories,

* Any biproduct satisfies the equality
  `total : ∑ j : J, biproduct.π f j ≫ biproduct.ι f j = 𝟙 (⨁ f)`,
  or, in the binary case, `total : fst ≫ inl + snd ≫ inr = 𝟙 X`.

* Any (binary) `product` or (binary) `coproduct` is a (binary) `biproduct`.

* In any category (with zero morphisms), if `biprod.map f g` is an isomorphism,
  then both `f` and `g` are isomorphisms.

* If `f` is a morphism `X₁ ⊞ X₂ ⟶ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  then we can construct isomorphisms `L : X₁ ⊞ X₂ ≅ X₁ ⊞ X₂` and `R : Y₁ ⊞ Y₂ ≅ Y₁ ⊞ Y₂`
  so that `L.hom ≫ g ≫ R.hom` is diagonal (with `X₁ ⟶ Y₁` component still `f`),
  via Gaussian elimination.

* As a corollary of the previous two facts,
  if we have an isomorphism `X₁ ⊞ X₂ ≅ Y₁ ⊞ Y₂` whose `X₁ ⟶ Y₁` entry is an isomorphism,
  we can construct an isomorphism `X₂ ≅ Y₂`.

* If `f : W ⊞ X ⟶ Y ⊞ Z` is an isomorphism, either `𝟙 W = 0`,
  or at least one of the component maps `W ⟶ Y` and `W ⟶ Z` is nonzero.

* If `f : ⨁ S ⟶ ⨁ T` is an isomorphism,
  then every column (corresponding to a nonzero summand in the domain)
  has some nonzero matrix entry.

* A functor preserves a biproduct if and only if it preserves
  the corresponding product if and only if it preserves the corresponding coproduct.

There are connections between this material and the special case of the category whose morphisms are
matrices over a ring, in particular the Schur complement (see
`Mathlib/LinearAlgebra/Matrix/SchurComplement.lean`). In particular, the declarations
`CategoryTheory.Biprod.isoElim`, `CategoryTheory.Biprod.gaussian`
and `Matrix.invertibleOfFromBlocks₁₁Invertible` are all closely related.

-/

open CategoryTheory

open CategoryTheory.Preadditive

open CategoryTheory.Limits

open CategoryTheory.Functor

open CategoryTheory.Preadditive

universe v v' u u'

noncomputable section

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Preadditive C]

namespace Limits

section Fintype

variable {J : Type*} [Fintype J]

set_option backward.isDefEq.respectTransparency false in

def isBilimitOfTotal {f : J → C} (b : Bicone f) (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) :
    b.IsBilimit where
  isLimit :=
    { lift := fun s => ∑ j : J, s.π.app ⟨j⟩ ≫ b.ι j
      uniq := fun s m h => by
        rw [← Category.comp_id m]
        dsimp
        rw [← total, comp_sum]
        apply Finset.sum_congr rfl
        intro j _
        have reassoced : m ≫ Bicone.π b j ≫ Bicone.ι b j = s.π.app ⟨j⟩ ≫ Bicone.ι b j := by
          simpa using eq_whisker (h ⟨j⟩) _
        rw [reassoced]
      fac := fun s j => by
        classical
        cases j
        simp only [sum_comp, Category.assoc, Bicone.toCone_π_app, b.ι_π, comp_dite]
        simp }
  isColimit :=
    { desc := fun s => ∑ j : J, b.π j ≫ s.ι.app ⟨j⟩
      uniq := fun s m h => by
        rw [← Category.id_comp m]
        dsimp
        rw [← total, sum_comp]
        apply Finset.sum_congr rfl
        intro j _
        simpa using b.π j ≫= h ⟨j⟩
      fac := fun s j => by
        classical
        cases j
        simp only [comp_sum, ← Category.assoc, Bicone.toCocone_ι_app, b.ι_π, dite_comp]
        simp }

theorem IsBilimit.total {f : J → C} {b : Bicone f} (i : b.IsBilimit) :
    ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt :=
  i.isLimit.hom_ext fun j => by
    classical
    cases j
    simp [sum_comp, b.ι_π, comp_dite]

theorem hasBiproduct_of_total {f : J → C} (b : Bicone f)
    (total : ∑ j : J, b.π j ≫ b.ι j = 𝟙 b.pt) : HasBiproduct f :=
  HasBiproduct.mk
    { bicone := b
      isBilimit := isBilimitOfTotal b total }

def isBilimitOfIsLimit {f : J → C} (t : Bicone f) (ht : IsLimit t.toCone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      classical
      cases j
      simp [sum_comp, t.ι_π, comp_dite]

def biconeIsBilimitOfLimitConeOfIsLimit {f : J → C} {t : Cone (Discrete.functor f)}
    (ht : IsLimit t) : (Bicone.ofLimitCone ht).IsBilimit :=
  isBilimitOfIsLimit _ <| IsLimit.ofIsoLimit ht <| Cone.ext (Iso.refl _) (by simp)

set_option backward.isDefEq.respectTransparency false in

def isBilimitOfIsColimit {f : J → C} (t : Bicone f) (ht : IsColimit t.toCocone) : t.IsBilimit :=
  isBilimitOfTotal _ <|
    ht.hom_ext fun j => by
      classical
      cases j
      simp_rw [Bicone.toCocone_ι_app, comp_sum, ← Category.assoc, t.ι_π, dite_comp]
      simp

def biconeIsBilimitOfColimitCoconeOfIsColimit {f : J → C} {t : Cocone (Discrete.functor f)}
    (ht : IsColimit t) : (Bicone.ofColimitCocone ht).IsBilimit :=
  isBilimitOfIsColimit _ <| IsColimit.ofIsoColimit ht <| Cocone.ext (Iso.refl _) <| by
    simp

end Fintype

section Finite

variable {J : Type*} [Finite J]

theorem HasBiproduct.of_hasProduct (f : J → C) [HasProduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfLimitConeOfIsLimit (limit.isLimit _) }

theorem HasBiproduct.of_hasCoproduct (f : J → C) [HasCoproduct f] : HasBiproduct f := by
  cases nonempty_fintype J
  exact HasBiproduct.mk
    { bicone := _
      isBilimit := biconeIsBilimitOfColimitCoconeOfIsColimit (colimit.isColimit _) }

end Finite

theorem HasFiniteBiproducts.of_hasFiniteProducts [HasFiniteProducts C] : HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasProduct _ }⟩

theorem HasFiniteBiproducts.of_hasFiniteCoproducts [HasFiniteCoproducts C] :
    HasFiniteBiproducts C :=
  ⟨fun _ => { has_biproduct := fun _ => HasBiproduct.of_hasCoproduct _ }⟩

section HasBiproduct

variable {J : Type} [Fintype J] {f : J → C} [HasBiproduct f]
