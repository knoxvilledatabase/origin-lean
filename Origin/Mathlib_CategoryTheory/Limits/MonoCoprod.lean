/-
Extracted from CategoryTheory/Limits/MonoCoprod.lean
Genuine: 3 of 8 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core

/-!

# Categories where inclusions into coproducts are monomorphisms

If `C` is a category, the class `MonoCoprod C` expresses that left
inclusions `A ⟶ A ⨿ B` are monomorphisms when `HasCoproduct A B`
holds. If so, it is shown that right inclusions are
also monomorphisms.

More generally, we deduce that when suitable coproducts exist, then
if `X : I → C` and `ι : J → I` is an injective map,
then the canonical morphism `∐ (X ∘ ι) ⟶ ∐ X` is a monomorphism.
It also follows that for any `i : I`, `Sigma.ι X i : X i ⟶ ∐ X` is
a monomorphism.

TODO: define distributive categories, and show that they satisfy `MonoCoprod`, see
<https://ncatlab.org/toddtrimble/published/distributivity+implies+monicity+of+coproduct+inclusions>

-/

noncomputable section

universe u

namespace CategoryTheory

open CategoryTheory.Category CategoryTheory.Limits

namespace Limits

variable (C : Type*) [Category* C]

class MonoCoprod : Prop where
  /-- the left inclusion of a colimit binary cofan is mono -/
  binaryCofan_inl : ∀ ⦃A B : C⦄ (c : BinaryCofan A B) (_ : IsColimit c), Mono c.inl

variable {C}

-- INSTANCE (free from Core): (priority

namespace MonoCoprod

set_option backward.isDefEq.respectTransparency false in

theorem binaryCofan_inr {A B : C} [MonoCoprod C] (c : BinaryCofan A B) (hc : IsColimit c) :
    Mono c.inr := by
  haveI hc' : IsColimit (BinaryCofan.mk c.inr c.inl) :=
    BinaryCofan.IsColimit.mk _ (fun f₁ f₂ => hc.desc (BinaryCofan.mk f₂ f₁))
      (by simp) (by simp)
      (fun f₁ f₂ m h₁ h₂ => BinaryCofan.IsColimit.hom_ext hc (by cat_disch) (by cat_disch))
  exact binaryCofan_inl _ hc'

-- INSTANCE (free from Core): {A

-- INSTANCE (free from Core): {A

theorem mono_inl_iff {A B : C} {c₁ c₂ : BinaryCofan A B} (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂) :
    Mono c₁.inl ↔ Mono c₂.inl := by
  suffices
    ∀ (c₁ c₂ : BinaryCofan A B) (_ : IsColimit c₁) (_ : IsColimit c₂) (_ : Mono c₁.inl),
      Mono c₂.inl
    by exact ⟨fun h₁ => this _ _ hc₁ hc₂ h₁, fun h₂ => this _ _ hc₂ hc₁ h₂⟩
  intro c₁ c₂ hc₁ hc₂ _
  simpa only [IsColimit.comp_coconePointUniqueUpToIso_hom] using
    mono_comp c₁.inl (hc₁.coconePointUniqueUpToIso hc₂).hom

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): monoCoprodType

variable {I₁ I₂ : Type*} {X : I₁ ⊕ I₂ → C} (c : Cofan X)
  (c₁ : Cofan (X ∘ Sum.inl)) (c₂ : Cofan (X ∘ Sum.inr))
  (hc : IsColimit c) (hc₁ : IsColimit c₁) (hc₂ : IsColimit c₂)

include hc hc₁ hc₂
