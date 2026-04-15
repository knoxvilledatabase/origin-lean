/-
Extracted from RingTheory/Finiteness/FinitePresentationLocal.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# `Algebra.FinitePresentation` is local

In this file we show that being a finitely presented algebra is local.

## Main results

- `Algebra.FinitePresentation.of_span_eq_top_target`: finite presentation is local on the
  (algebraic) target

-/

open scoped Pointwise TensorProduct

namespace Algebra.FinitePresentation

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

lemma of_span_eq_top_target_aux {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FinitePresentation R A] (f : A →ₐ[R] S) (hf : Function.Surjective f)
    (t : Finset A) (ht : Ideal.span (t : Set A) = ⊤)
    (H : ∀ g : t, Algebra.FinitePresentation R (Localization.Away (f g))) :
    Algebra.FinitePresentation R S := by
  apply Algebra.FinitePresentation.of_surjective hf
  apply RingHom.ker_fg_of_localizationSpan t ht
  intro g
  let f' : Localization.Away g.val →ₐ[R] Localization.Away (f g) :=
    Localization.awayMapₐ f g.val
  have (g : t) : Algebra.FinitePresentation R (Localization.Away g.val) :=
    haveI : Algebra.FinitePresentation A (Localization.Away g.val) :=
      IsLocalization.Away.finitePresentation g.val
    Algebra.FinitePresentation.trans R A (Localization.Away g.val)
  apply Algebra.FinitePresentation.ker_fG_of_surjective f'
  exact IsLocalization.Away.mapₐ_surjective_of_surjective _ hf

universe u

lemma of_span_eq_top_target_of_isLocalizationAway {ι : Type*} (s : ι → S)
    (hs : Ideal.span (Set.range s) = ⊤) (T : ι → Type*) [∀ i, CommRing (T i)] [∀ i, Algebra R (T i)]
    [∀ i, Algebra S (T i)] [∀ i, IsScalarTower R S (T i)] [∀ i, IsLocalization.Away (s i) (T i)]
    [∀ i, Algebra.FinitePresentation R (T i)] :
    Algebra.FinitePresentation R S := by
  apply of_span_eq_top_target _ hs
  rintro - ⟨i, rfl⟩
  exact .equiv <| (IsLocalization.algEquiv (.powers <| s i) _ (T i)).symm |>.restrictScalars R

-- INSTANCE (free from Core): pi

end Algebra.FinitePresentation
