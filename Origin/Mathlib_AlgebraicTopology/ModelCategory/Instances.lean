/-
Extracted from AlgebraicTopology/ModelCategory/Instances.lean
Genuine: 10 of 53 | Dissolved: 0 | Infrastructure: 43
-/
import Origin.Core

/-!
# Consequences of model category axioms

In this file, we deduce basic properties of fibrations, cofibrations,
and weak equivalences from the axioms of model categories.

-/

universe w v u

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable (C : Type u) [Category.{v} C]

-- INSTANCE (free from Core): [CategoryWithWeakEquivalences

-- INSTANCE (free from Core): [CategoryWithWeakEquivalences

section IsStableUnderComposition

variable {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

-- INSTANCE (free from Core): [CategoryWithCofibrations

-- INSTANCE (free from Core): [CategoryWithFibrations

-- INSTANCE (free from Core): [CategoryWithWeakEquivalences

end IsStableUnderComposition

variable [CategoryWithWeakEquivalences C]

section HasTwoOutOfThreeProperty

variable [(weakEquivalences C).HasTwoOutOfThreeProperty]
  {C} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

lemma weakEquivalence_of_postcomp
    [hg : WeakEquivalence g] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence f := by
  rw [weakEquivalence_iff] at hg hfg ⊢
  exact of_postcomp _ _ _ hg hfg

lemma weakEquivalence_of_precomp
    [hf : WeakEquivalence f] [hfg : WeakEquivalence (f ≫ g)] :
    WeakEquivalence g := by
  rw [weakEquivalence_iff] at hf hfg ⊢
  exact of_precomp _ _ _ hf hfg

lemma weakEquivalence_postcomp_iff [WeakEquivalence g] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence f :=
  ⟨fun _ ↦ weakEquivalence_of_postcomp f g, fun _ ↦ inferInstance⟩

lemma weakEquivalence_precomp_iff [WeakEquivalence f] :
    WeakEquivalence (f ≫ g) ↔ WeakEquivalence g :=
  ⟨fun _ ↦ weakEquivalence_of_precomp f g, fun _ ↦ inferInstance⟩

variable {f g} {fg : X ⟶ Z}

lemma weakEquivalence_of_postcomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence g] [hfg : WeakEquivalence fg] :
    WeakEquivalence f := by
  subst fac
  exact weakEquivalence_of_postcomp f g

lemma weakEquivalence_of_precomp_of_fac (fac : f ≫ g = fg)
    [WeakEquivalence f] [WeakEquivalence fg] :
    WeakEquivalence g := by
  subst fac
  exact weakEquivalence_of_precomp f g

end HasTwoOutOfThreeProperty

variable [CategoryWithCofibrations C] [CategoryWithFibrations C]

variable [IsWeakFactorizationSystem (trivialCofibrations C) (fibrations C)]

lemma fibrations_llp :
    (fibrations C).llp = trivialCofibrations C :=
  llp_eq_of_wfs _ _

lemma trivialCofibrations_rlp :
    (trivialCofibrations C).rlp = fibrations C :=
  rlp_eq_of_wfs _ _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (J : Type w)

-- INSTANCE (free from Core): isStableUnderCoproductsOfShape_trivialCofibrations

-- INSTANCE (free from Core): isStableUnderProductsOfShape_fibrations

end

variable [IsWeakFactorizationSystem (cofibrations C) (trivialFibrations C)]

lemma trivialFibrations_llp :
    (trivialFibrations C).llp = cofibrations C :=
  llp_eq_of_wfs _ _

lemma cofibrations_rlp :
    (cofibrations C).rlp = trivialFibrations C :=
  rlp_eq_of_wfs _ _

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable (J : Type w)

-- INSTANCE (free from Core): isStableUnderCoproductsOfShape_cofibrations

-- INSTANCE (free from Core): isStableUnderProductsOfShape_trivialFibrations

end

section Pullbacks

variable {X Y Z : C} (f : X ⟶ Y) (g : X ⟶ Z) [HasPushout f g]

-- INSTANCE (free from Core): [(cofibrations

-- INSTANCE (free from Core): [(cofibrations

-- INSTANCE (free from Core): [(trivialCofibrations

-- INSTANCE (free from Core): [(trivialCofibrations

end

variable {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g]

-- INSTANCE (free from Core): [(fibrations

-- INSTANCE (free from Core): [(fibrations

-- INSTANCE (free from Core): [(trivialFibrations

-- INSTANCE (free from Core): [(trivialFibrations

end

end Pullbacks

section Products

variable (J : Type w) {C J} {X Y : J → C} (f : ∀ i, X i ⟶ Y i)

variable [HasCoproduct X] [HasCoproduct Y] [h : ∀ i, Cofibration (f i)]

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

end

variable [HasProduct X] [HasProduct Y] [h : ∀ i, Fibration (f i)]

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

end

end Products

section BinaryProducts

variable {X₁ X₂ Y₁ Y₂ : C} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

end BinaryProducts

section IsIso

variable {X Y : C} (f : X ⟶ Y)

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

end IsIso

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [IsWeakFactorizationSystem

-- INSTANCE (free from Core): [(weakEquivalences

section MapFactorizationData

variable {X Y : C} (f : X ⟶ Y)

variable (h : MapFactorizationData (cofibrations C) (trivialFibrations C) f)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

variable (h : MapFactorizationData (trivialCofibrations C) (fibrations C) f)

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end

end MapFactorizationData

end HomotopicalAlgebra
