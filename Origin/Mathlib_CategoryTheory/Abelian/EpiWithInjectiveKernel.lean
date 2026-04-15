/-
Extracted from CategoryTheory/Abelian/EpiWithInjectiveKernel.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Epimorphisms with an injective kernel

In this file, we define the class of morphisms `epiWithInjectiveKernel` in an
abelian category. We show that this property of morphisms is multiplicative.

This shall be used in the file `Mathlib/Algebra/Homology/Factorizations/Basic.lean` in
order to define morphisms of cochain complexes which satisfy this property
degreewise.

-/

namespace CategoryTheory

open Category Limits ZeroObject Preadditive

variable {C : Type*} [Category* C] [Abelian C]

namespace Abelian

def epiWithInjectiveKernel : MorphismProperty C :=
  fun _ _ f => Epi f ∧ Injective (kernel f)

lemma epiWithInjectiveKernel_iff {X Y : C} (g : X ⟶ Y) :
    epiWithInjectiveKernel g ↔ ∃ (I : C) (_ : Injective I) (f : I ⟶ X) (w : f ≫ g = 0),
      Nonempty (ShortComplex.mk f g w).Splitting := by
  constructor
  · rintro ⟨_, _⟩
    let S := ShortComplex.mk (kernel.ι g) g (by simp)
    exact ⟨_, inferInstance, _, S.zero,
      ⟨ShortComplex.Splitting.ofExactOfRetraction S
        (S.exact_of_f_is_kernel (kernelIsKernel g)) (Injective.factorThru (𝟙 _) (kernel.ι g))
        (by simp [S]) inferInstance⟩⟩
  · rintro ⟨I, _, f, w, ⟨σ⟩⟩
    have : IsSplitEpi g := ⟨σ.s, σ.s_g⟩
    let e : I ≅ kernel g :=
      IsLimit.conePointUniqueUpToIso σ.shortExact.fIsKernel (limit.isLimit _)
    exact ⟨inferInstance, Injective.of_iso e inferInstance⟩

lemma epiWithInjectiveKernel_of_iso {X Y : C} (f : X ⟶ Y) [IsIso f] :
    epiWithInjectiveKernel f := by
  rw [epiWithInjectiveKernel_iff]
  exact ⟨0, inferInstance, 0, by simp,
    ⟨ShortComplex.Splitting.ofIsZeroOfIsIso _ (isZero_zero C) (by assumption)⟩⟩

-- INSTANCE (free from Core): :

end Abelian

end CategoryTheory
