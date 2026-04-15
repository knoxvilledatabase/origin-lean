/-
Extracted from CategoryTheory/Quotient/Preadditive.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.CategoryTheory.Quotient
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The quotient category is preadditive

If an equivalence relation `r : HomRel C` on the morphisms of a preadditive category
is compatible with the addition, then the quotient category `Quotient r` is also
preadditive.

-/

namespace CategoryTheory

namespace Quotient

variable {C : Type _} [Category C] [Preadditive C] (r : HomRel C) [Congruence r]

namespace Preadditive

def add (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
    {X Y : Quotient r} (f g : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn₂ f g (fun a b => Quot.mk _ (a + b))
    (fun f g₁ g₂ h₁₂ => by
      simp only [compClosure_iff_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ (Congruence.equivalence.refl f) h₁₂)
    (fun f₁ f₂ g h₁₂ => by
      simp only [compClosure_iff_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ h₁₂ (Congruence.equivalence.refl g))

def neg (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
    {X Y : Quotient r} (f : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn f (fun a => Quot.mk _ (-a))
    (fun f g => by
      intro hfg
      simp only [compClosure_iff_self] at hfg
      erw [functor_map_eq_iff]
      apply Congruence.equivalence.symm
      convert hr f g _ _ hfg (Congruence.equivalence.refl (-f-g)) using 1 <;> abel)

end Preadditive

def preadditive
    (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂)) :
    Preadditive (Quotient r) where
  homGroup P Q :=
    let iZ : Zero (P ⟶ Q) :=
      { zero := Quot.mk _ 0 }
    let iA : Add (P ⟶ Q) :=
      { add := Preadditive.add r hr }
    let iN : Neg (P ⟶ Q) :=
      { neg := Preadditive.neg r hr }
    { add_assoc := by rintro ⟨_⟩ ⟨_⟩ ⟨_⟩; exact congr_arg (functor r).map (add_assoc _ _ _)
      zero_add := by rintro ⟨_⟩; exact congr_arg (functor r).map (zero_add _)
      add_zero := by rintro ⟨_⟩; exact congr_arg (functor r).map (add_zero _)
      add_comm := by rintro ⟨_⟩ ⟨_⟩; exact congr_arg (functor r).map (add_comm _ _)
      neg_add_cancel := by rintro ⟨_⟩; exact congr_arg (functor r).map (neg_add_cancel _)
      -- todo: use a better defeq
      nsmul := nsmulRec
      zsmul := zsmulRec }
  add_comp := by
    rintro _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact congr_arg (functor r).map (by apply Preadditive.add_comp)
  comp_add := by
    rintro _ _ _ ⟨_⟩ ⟨_⟩ ⟨_⟩
    exact congr_arg (functor r).map (by apply Preadditive.comp_add)

lemma functor_additive
    (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂)) :
    letI := preadditive r hr
    (functor r).Additive :=
  letI := preadditive r hr
  { map_add := rfl }

end Quotient

end CategoryTheory
