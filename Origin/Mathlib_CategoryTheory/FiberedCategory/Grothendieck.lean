/-
Extracted from CategoryTheory/FiberedCategory/Grothendieck.lean
Genuine: 4 of 7 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# The Grothendieck construction gives a fibered category

In this file we show that the Grothendieck construction applied to a pseudofunctor `F`
gives a fibered category over the base category.

We also provide a `HasFibers` instance to `∫ᶜ F`, such that the fiber over `S` is the
category `F(S)`.

## References
[Vistoli2008] "Notes on Grothendieck Topologies, Fibered Categories and Descent Theory" by
Angelo Vistoli

-/

namespace CategoryTheory.Pseudofunctor.CoGrothendieck

open Functor Opposite Bicategory Fiber

variable {𝒮 : Type*} [Category* 𝒮] {F : LocallyDiscrete 𝒮ᵒᵖ ⥤ᵖ Cat}

variable {R S : 𝒮} (a : F.obj ⟨op S⟩) (f : R ⟶ S)

abbrev domainCartesianLift : ∫ᶜ F := ⟨R, (F.map f.op.toLoc).toFunctor.obj a⟩

abbrev cartesianLift : domainCartesianLift a f ⟶ ⟨S, a⟩ := ⟨f, 𝟙 _⟩

-- INSTANCE (free from Core): isHomLift_cartesianLift

variable {a} in

abbrev homCartesianLift {a' : ∫ᶜ F} (g : a'.1 ⟶ R) (φ' : a' ⟶ ⟨S, a⟩)
    [IsHomLift (forget F) (g ≫ f) φ'] : a' ⟶ domainCartesianLift a f where
  base := g
  fiber :=
    have : φ'.base = g ≫ f := by simpa using IsHomLift.fac' (forget F) (g ≫ f) φ'
    φ'.fiber ≫ eqToHom (by simp [this]) ≫ (F.mapComp f.op.toLoc g.op.toLoc).hom.toNatTrans.app a

-- INSTANCE (free from Core): isHomLift_homCartesianLift

set_option backward.isDefEq.respectTransparency false in

lemma isStronglyCartesian_homCartesianLift :
    IsStronglyCartesian (forget F) f (cartesianLift a f) where
  universal_property' {a'} g φ' hφ' := by
    refine ⟨homCartesianLift f g φ', ⟨inferInstance, ?_⟩, ?_⟩
    · exact Hom.ext _ _ (by simpa using IsHomLift.fac (forget F) (g ≫ f) φ')
        (by simp [← Cat.Hom₂.comp_app])
    rintro χ' ⟨hχ'.symm, rfl⟩
    obtain ⟨rfl⟩ : g = χ'.1 := by simpa using IsHomLift.fac (forget F) g χ'
    ext <;> simp [← Cat.Hom₂.comp_app]

end

-- INSTANCE (free from Core): :

variable (F) (S : 𝒮)

set_option backward.isDefEq.respectTransparency false in

attribute [local simp] PrelaxFunctor.map₂_eqToHom in
