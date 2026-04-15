/-
Extracted from Algebra/Homology/Double.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A homological complex lying in two degrees

Given `c : ComplexShape ι`, distinct indices `i₀` and `i₁` such that `hi₀₁ : c.Rel i₀ i₁`,
we construct a homological complex `double f hi₀₁` for any morphism `f : X₀ ⟶ X₁`.
It consists of the objects `X₀` and `X₁` in degrees `i₀` and `i₁`, respectively,
with the differential `X₀ ⟶ X₁` given by `f`, and zero everywhere else.

-/

open CategoryTheory Category Limits ZeroObject Opposite

namespace HomologicalComplex

variable {C : Type*} [Category* C] [HasZeroMorphisms C] [HasZeroObject C]

variable {X₀ X₁ : C} (f : X₀ ⟶ X₁) {ι : Type*} {c : ComplexShape ι}
  {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁)

open Classical in

noncomputable def double : HomologicalComplex C c where
  X k := if k = i₀ then X₀ else if k = i₁ then X₁ else 0
  d k k' :=
    if hk : k = i₀ ∧ k' = i₁ ∧ i₀ ≠ i₁ then
      eqToHom (if_pos hk.1) ≫ f ≫ eqToHom (by
        rw [if_neg, if_pos hk.2.1]
        aesop)
    else 0
  d_comp_d' := by
    rintro i j k hij hjk
    dsimp
    by_cases hi : i = i₀
    · subst hi
      by_cases hj : j = i₁
      · subst hj
        nth_rw 2 [dif_neg (by tauto)]
        rw [comp_zero]
      · rw [dif_neg (by tauto), zero_comp]
    · rw [dif_neg (by tauto), zero_comp]
  shape i j hij := dif_neg (by aesop)

lemma isZero_double_X (k : ι) (h₀ : k ≠ i₀) (h₁ : k ≠ i₁) :
    IsZero ((double f hi₀₁).X k) := by
  dsimp [double]
  rw [if_neg h₀, if_neg h₁]
  exact Limits.isZero_zero C

noncomputable def doubleXIso₀ : (double f hi₀₁).X i₀ ≅ X₀ :=
  eqToIso (dif_pos rfl)

noncomputable def doubleXIso₁ (h : i₀ ≠ i₁) : (double f hi₀₁).X i₁ ≅ X₁ :=
  eqToIso (by
    dsimp [double]
    rw [if_neg h.symm, if_pos rfl])

lemma double_d (h : i₀ ≠ i₁) :
    (double f hi₀₁).d i₀ i₁ =
      (doubleXIso₀ f hi₀₁).hom ≫ f ≫ (doubleXIso₁ f hi₀₁ h).inv :=
  dif_pos ⟨rfl, rfl, h⟩

lemma double_d_eq_zero₀ (a b : ι) (ha : a ≠ i₀) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by tauto)

lemma double_d_eq_zero₁ (a b : ι) (hb : b ≠ i₁) :
    (double f hi₀₁).d a b = 0 :=
  dif_neg (by tauto)

variable {f hi₀₁} in
