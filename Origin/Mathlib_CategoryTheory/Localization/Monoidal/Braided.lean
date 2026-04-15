/-
Extracted from CategoryTheory/Localization/Monoidal/Braided.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!

# Localization of symmetric monoidal categories

Let `C` be a monoidal category equipped with a class of morphisms `W` which
is compatible with the monoidal category structure. The file
`Mathlib.CategoryTheory.Localization.Monoidal.Basic` constructs a monoidal structure on
the localized on `D` such that the localization functor is monoidal.

In this file we promote this monoidal structure to a braided structure in the case where `C` is
braided, in such a way that the localization functor is braided. If `C` is symmetric monoidal, then
the monoidal structure on `D` is also symmetric.
-/

open CategoryTheory Category MonoidalCategory BraidedCategory Functor

namespace CategoryTheory.Localization.Monoidal

variable {C D : Type*} [Category* C] [Category* D] (L : C ⥤ D) (W : MorphismProperty C)
  [MonoidalCategory C] [W.IsMonoidal] [L.IsLocalization W]
  {unit : D} (ε : L.obj (𝟙_ C) ≅ unit)

local notation "L'" => toMonoidalCategory L W ε

-- INSTANCE (free from Core): :

section Braided

variable [BraidedCategory C]

-- INSTANCE (free from Core): :

noncomputable def braidingNatIso : tensorBifunctor L W ε ≅ (tensorBifunctor L W ε).flip :=
  lift₂NatIso L' L' W W
    ((curriedTensor C) ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L')
    (((curriedTensor C).flip ⋙ (whiskeringRight C C
      (LocalizedMonoidal L W ε)).obj L'))
    _ _ (isoWhiskerRight (curriedBraidingNatIso C) _)

lemma braidingNatIso_hom_app (X Y : C) :
    ((braidingNatIso L W ε).hom.app ((L').obj X)).app ((L').obj Y) =
      (Functor.LaxMonoidal.μ (L') X Y) ≫
        (L').map (β_ X Y).hom ≫
          (Functor.OplaxMonoidal.δ (L') Y X) := by
  simp [braidingNatIso, lift₂NatIso]
  rfl
