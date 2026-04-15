/-
Extracted from CategoryTheory/Functor/ReflectsIso/Balanced.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Balanced categories and functors reflecting isomorphisms

If a category is `C`, and a functor out of `C` reflects epimorphisms and monomorphisms,
then the functor reflects isomorphisms.
Furthermore, categories that admit a functor that `ReflectsIsomorphisms`, `PreservesEpimorphisms`
and `PreservesMonomorphisms` are balanced.

-/

open CategoryTheory CategoryTheory.Functor

namespace CategoryTheory

variable {C : Type*} [Category* C]
  {D : Type*} [Category* D]

-- INSTANCE (free from Core): (priority

lemma Functor.balanced_of_preserves (F : C ⥤ D)
    [F.ReflectsIsomorphisms] [F.PreservesEpimorphisms] [F.PreservesMonomorphisms] [Balanced D] :
    Balanced C where
  isIso_of_mono_of_epi f _ _ := by
    rw [← isIso_iff_of_reflects_iso (F := F)]
    exact isIso_of_mono_of_epi _

end CategoryTheory
