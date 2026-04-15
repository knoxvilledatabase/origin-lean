/-
Extracted from CategoryTheory/Limits/Shapes/StrongEpi.lean
Genuine: 16 of 26 | Dissolved: 0 | Infrastructure: 10
-/
import Origin.Core

/-!
# Strong epimorphisms

In this file, we define strong epimorphisms. A strong epimorphism is an epimorphism `f`
which has the (unique) left lifting property with respect to monomorphisms. Similarly,
a strong monomorphism is a monomorphism which has the (unique) right lifting property
with respect to epimorphisms.

## Main results

Besides the definition, we show that
* the composition of two strong epimorphisms is a strong epimorphism,
* if `f ≫ g` is a strong epimorphism, then so is `g`,
* if `f` is both a strong epimorphism and a monomorphism, then it is an isomorphism

We also define classes `StrongMonoCategory` and `StrongEpiCategory` for categories in which
every monomorphism or epimorphism is strong, and deduce that these categories are balanced.

## TODO

Show that the dual of a strong epimorphism is a strong monomorphism, and vice versa.

## References

* [F. Borceux, *Handbook of Categorical Algebra 1*][borceux-vol1]
-/

universe v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

variable {P Q : C}

class StrongEpi (f : P ⟶ Q) : Prop where
  /-- The epimorphism condition on `f` -/
  epi : Epi f
  /-- The left lifting property with respect to all monomorphisms -/
  llp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Mono z], HasLiftingProperty f z

theorem StrongEpi.mk' {f : P ⟶ Q} [Epi f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y)
      (_ : Mono z) (u : P ⟶ X) (v : Q ⟶ Y) (sq : CommSq u f z v), sq.HasLift) :
    StrongEpi f :=
  { epi := inferInstance
    llp := fun {X Y} z hz => ⟨fun {u v} sq => hf X Y z hz u v sq⟩ }

class StrongMono (f : P ⟶ Q) : Prop where
  /-- The monomorphism condition on `f` -/
  mono : Mono f
  /-- The right lifting property with respect to all epimorphisms -/
  rlp : ∀ ⦃X Y : C⦄ (z : X ⟶ Y) [Epi z], HasLiftingProperty z f

theorem StrongMono.mk' {f : P ⟶ Q} [Mono f]
    (hf : ∀ (X Y : C) (z : X ⟶ Y) (_ : Epi z) (u : X ⟶ P)
      (v : Y ⟶ Q) (sq : CommSq u z f v), sq.HasLift) : StrongMono f where
  mono := inferInstance
  rlp := fun {X Y} z hz => ⟨fun {u v} sq => hf X Y z hz u v sq⟩

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): 100]

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

variable {R : C} (f : P ⟶ Q) (g : Q ⟶ R)

-- INSTANCE (free from Core): strongEpi_comp

-- INSTANCE (free from Core): strongMono_comp

theorem strongEpi_of_strongEpi [StrongEpi (f ≫ g)] : StrongEpi g :=
  { epi := epi_of_epi f g
    llp := fun {X Y} z _ => by
      constructor
      intro u v sq
      have h₀ : (f ≫ u) ≫ z = (f ≫ g) ≫ v := by simp only [Category.assoc, sq.w]
      exact
        CommSq.HasLift.mk'
          ⟨(CommSq.mk h₀).lift, by
            simp only [← cancel_mono z, Category.assoc, CommSq.fac_right, sq.w], by simp⟩ }

theorem strongMono_of_strongMono [StrongMono (f ≫ g)] : StrongMono f :=
  { mono := mono_of_mono f g
    rlp := fun {X Y} z => by
      intros
      constructor
      intro u v sq
      have h₀ : u ≫ f ≫ g = z ≫ v ≫ g := by
        rw [← Category.assoc, eq_whisker sq.w, Category.assoc]
      exact CommSq.HasLift.mk' ⟨(CommSq.mk h₀).lift, by simp, by simp [← cancel_epi z, sq.w]⟩ }

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

theorem StrongEpi.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongEpi f] : StrongEpi g :=
  { epi := by
      rw [Arrow.iso_w' e]
      infer_instance
    llp := fun {X Y} z => by
      intro
      apply HasLiftingProperty.of_arrow_iso_left e z }

set_option backward.isDefEq.respectTransparency false in

theorem StrongMono.of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) [h : StrongMono f] : StrongMono g :=
  { mono := by
      rw [Arrow.iso_w' e]
      infer_instance
    rlp := fun {X Y} z => by
      intro
      apply HasLiftingProperty.of_arrow_iso_right z e }

theorem StrongEpi.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongEpi f ↔ StrongEpi g := by
  constructor <;> intro
  exacts [StrongEpi.of_arrow_iso e, StrongEpi.of_arrow_iso e.symm]

theorem StrongMono.iff_of_arrow_iso {A B A' B' : C} {f : A ⟶ B} {g : A' ⟶ B'}
    (e : Arrow.mk f ≅ Arrow.mk g) : StrongMono f ↔ StrongMono g := by
  constructor <;> intro
  exacts [StrongMono.of_arrow_iso e, StrongMono.of_arrow_iso e.symm]

end

theorem isIso_of_mono_of_strongEpi (f : P ⟶ Q) [Mono f] [StrongEpi f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

theorem isIso_of_epi_of_strongMono (f : P ⟶ Q) [Epi f] [StrongMono f] : IsIso f :=
  ⟨⟨(CommSq.mk (show 𝟙 P ≫ f = f ≫ 𝟙 Q by simp)).lift, by simp⟩⟩

variable (C)

class StrongEpiCategory : Prop where
  /-- A strong epi category is a category in which every epimorphism is strong. -/
  strongEpi_of_epi : ∀ {X Y : C} (f : X ⟶ Y) [Epi f], StrongEpi f

class StrongMonoCategory : Prop where
  /-- A strong mono category is a category in which every monomorphism is strong. -/
  strongMono_of_mono : ∀ {X Y : C} (f : X ⟶ Y) [Mono f], StrongMono f

end

theorem strongEpi_of_epi [StrongEpiCategory C] (f : P ⟶ Q) [Epi f] : StrongEpi f :=
  StrongEpiCategory.strongEpi_of_epi _

theorem strongMono_of_mono [StrongMonoCategory C] (f : P ⟶ Q) [Mono f] : StrongMono f :=
  StrongMonoCategory.strongMono_of_mono _

attribute [local instance] strongEpi_of_epi

-- INSTANCE (free from Core): (priority

end

attribute [local instance] strongMono_of_mono

-- INSTANCE (free from Core): (priority

end

end CategoryTheory
