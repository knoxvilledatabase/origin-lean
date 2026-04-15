/-
Extracted from CategoryTheory/Quotient/Preadditive.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The quotient category is preadditive

If an equivalence relation `r : HomRel C` on the morphisms of a preadditive category
is compatible with the addition, then the quotient category `Quotient r` is also
preadditive.

-/

namespace CategoryTheory

namespace Quotient

variable {C : Type _} [Category* C] [Preadditive C] (r : HomRel C) [Congruence r]

namespace Preadditive

def add (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
    {X Y : Quotient r} (f g : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn₂ f g (fun a b => Quot.mk _ (a + b))
    (fun f g₁ g₂ h₁₂ => by
      simp only [HomRel.compClosure_iff_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ (Congruence.equivalence.refl f) h₁₂)
    (fun f₁ f₂ g h₁₂ => by
      simp only [HomRel.compClosure_iff_self] at h₁₂
      erw [functor_map_eq_iff]
      exact hr _ _ _ _ h₁₂ (Congruence.equivalence.refl g))

def neg (hr : ∀ ⦃X Y : C⦄ (f₁ f₂ g₁ g₂ : X ⟶ Y) (_ : r f₁ f₂) (_ : r g₁ g₂), r (f₁ + g₁) (f₂ + g₂))
    {X Y : Quotient r} (f : X ⟶ Y) : X ⟶ Y :=
  Quot.liftOn f (fun a => Quot.mk _ (-a))
    (fun f g => by
      intro hfg
      simp only [HomRel.compClosure_iff_self] at hfg
      erw [functor_map_eq_iff]
      apply Congruence.equivalence.symm
      convert hr f g _ _ hfg (Congruence.equivalence.refl (-f - g)) using 1 <;> abel)

end Preadditive
