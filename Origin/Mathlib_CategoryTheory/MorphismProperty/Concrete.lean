/-
Extracted from CategoryTheory/MorphismProperty/Concrete.lean
Genuine: 7 of 15 | Dissolved: 0 | Infrastructure: 8
-/
import Origin.Core

/-!
# Morphism properties defined in concrete categories

In this file, we define the class of morphisms `MorphismProperty.injective`,
`MorphismProperty.surjective`, `MorphismProperty.bijective` in concrete
categories, and show that it is stable under composition and respects isomorphisms.

We introduce type-classes `HasSurjectiveInjectiveFactorization` and
`HasFunctorialSurjectiveInjectiveFactorization` expressing that in a concrete category `C`,
all morphisms can be factored (resp. factored functorially) as a surjective map
followed by an injective map.

-/

universe v u

namespace CategoryTheory

variable (C : Type u) [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

namespace MorphismProperty

open Function

protected def injective : MorphismProperty C := fun _ _ f => Injective f

protected def surjective : MorphismProperty C := fun _ _ f => Surjective f

protected def bijective : MorphismProperty C := fun _ _ f => Bijective f

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): injective_respectsIso

-- INSTANCE (free from Core): surjective_respectsIso

-- INSTANCE (free from Core): bijective_respectsIso

end MorphismProperty

namespace ConcreteCategory

abbrev HasSurjectiveInjectiveFactorization :=
    (MorphismProperty.surjective C).HasFactorization (MorphismProperty.injective C)

abbrev HasFunctorialSurjectiveInjectiveFactorization :=
  (MorphismProperty.surjective C).HasFunctorialFactorization (MorphismProperty.injective C)

abbrev FunctorialSurjectiveInjectiveFactorizationData :=
  (MorphismProperty.surjective C).FunctorialFactorizationData (MorphismProperty.injective C)

end ConcreteCategory

open ConcreteCategory

def functorialSurjectiveInjectiveFactorizationData :
    FunctorialSurjectiveInjectiveFactorizationData (Type u) where
  Z :=
    { obj := fun f => Subtype (Set.range f.hom.hom)
      map := fun φ => TypeCat.ofHom fun y => ⟨φ.right y.1, by
        obtain ⟨_, x, rfl⟩ := y
        exact ⟨φ.left x, congr_hom φ.w x⟩ ⟩ }
  i :=
    { app := fun f => TypeCat.ofHom fun x => ⟨f.hom x, ⟨x, rfl⟩⟩
      naturality := fun f g φ => by
        ext x
        exact congr_hom φ.w x }
  p :=
    { app := fun _ => TypeCat.ofHom (fun y => y.1)
      naturality := by intros; rfl; }
  fac := rfl
  hi := by
    rintro f ⟨_, x, rfl⟩
    exact ⟨x, rfl⟩
  hp f x₁ x₂ h := by
    rw [Subtype.ext_iff]
    exact h

-- INSTANCE (free from Core): :

end CategoryTheory
