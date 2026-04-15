/-
Extracted from CategoryTheory/Shift/Induced.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shift induced from a category to another

In this file, we introduce a sufficient condition on a functor
`F : C ⥤ D` so that a shift on `C` by a monoid `A` induces a shift on `D`.
More precisely, when the functor `(D ⥤ D) ⥤ C ⥤ D` given
by the precomposition with `F` is fully faithful, and that
all the shift functors on `C` can be lifted to functors `D ⥤ D`
(i.e. we have functors `s a : D ⥤ D` for all `a : A`, and isomorphisms
`F ⋙ s a ≅ shiftFunctor C a ⋙ F`), then these functors `s a` are
the shift functors of a term of type `HasShift D A`.

As this condition on the functor `F` is satisfied for quotient and localization
functors, the main construction `HasShift.induced` in this file shall be
used for both quotient and localized shifts.

-/

namespace CategoryTheory

open Functor

variable {C D : Type _} [Category* C] [Category* D]
  (F : C ⥤ D) {A : Type _} [AddMonoid A] [HasShift C A]
  (s : A → D ⥤ D) (i : ∀ a, F ⋙ s a ≅ shiftFunctor C a ⋙ F)
  [((whiskeringLeft C D D).obj F).Full] [((whiskeringLeft C D D).obj F).Faithful]

namespace HasShift

namespace Induced

noncomputable def zero : s 0 ≅ 𝟭 D :=
  ((whiskeringLeft C D D).obj F).preimageIso ((i 0) ≪≫
    isoWhiskerRight (shiftFunctorZero C A) F ≪≫ F.leftUnitor ≪≫ F.rightUnitor.symm)

noncomputable def add (a b : A) : s (a + b) ≅ s a ⋙ s b :=
  ((whiskeringLeft C D D).obj F).preimageIso
    (i (a + b) ≪≫ isoWhiskerRight (shiftFunctorAdd C a b) F ≪≫
      Functor.associator _ _ _ ≪≫
        isoWhiskerLeft _ (i b).symm ≪≫ (Functor.associator _ _ _).symm ≪≫
        isoWhiskerRight (i a).symm _ ≪≫ Functor.associator _ _ _)
