/-
Extracted from CategoryTheory/Sites/Equivalence.lean
Genuine: 3 of 6 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Equivalences of sheaf categories

Given a site `(C, J)` and a category `D` which is equivalent to `C`, with `C` and `D` possibly large
and possibly in different universes, we transport the Grothendieck topology `J` on `C` to `D` and
prove that the sheaf categories are equivalent.

We also prove that sheafification and the property `HasSheafCompose` transport nicely over this
equivalence, and apply it to essentially small sites. We also provide instances for existence of
sufficiently small limits in the sheaf category on the essentially small site.

## Main definitions

* `CategoryTheory.Equivalence.sheafCongr` is the equivalence of sheaf categories.

* `CategoryTheory.Equivalence.transportAndSheafify` is the functor which takes a presheaf on `C`,
  transports it over the equivalence to `D`, sheafifies there and then transports back to `C`.

* `CategoryTheory.Equivalence.transportSheafificationAdjunction`: `transportAndSheafify` is
  left adjoint to the functor taking a sheaf to its underlying presheaf.

* `CategoryTheory.smallSheafify` is the functor which takes a presheaf on an essentially small site
  `(C, J)`, transports to a small model, sheafifies there and then transports back to `C`.

* `CategoryTheory.smallSheafificationAdjunction`: `smallSheafify` is left adjoint to the functor
  taking a sheaf to its underlying presheaf.

-/

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄ w

namespace CategoryTheory

open Functor Limits GrothendieckTopology

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C)

variable {D : Type u₂} [Category.{v₂} D] (K : GrothendieckTopology D) (e : C ≌ D) (G : D ⥤ C)

variable (A : Type u₃) [Category.{v₃} A]

namespace Equivalence

-- INSTANCE (free from Core): (priority

set_option backward.isDefEq.respectTransparency false in

-- INSTANCE (free from Core): :

lemma eq_inducedTopology_of_isDenseSubsite [e.inverse.IsDenseSubsite K J] :
    K = e.inverse.inducedTopology J := by
  ext
  exact (e.inverse.functorPushforward_mem_iff K J).symm

lemma isDenseSubsite_functor_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.functor.IsDenseSubsite J K where
  functorPushforward_mem_iff {X S} := by
    constructor
    · intro H
      refine J.superset_covering ?_ (e.functor.cover_lift J K H)
      rw [(Sieve.fullyFaithfulFunctorGaloisCoinsertion e.functor X).u_l_eq S]
    · intro H
      refine K.superset_covering ?_
        (e.inverse.cover_lift K J (J.pullback_stable (e.unitInv.app X) H))
      exact fun Y f (H : S _) ↦ ⟨_, _, e.counitInv.app Y, H, by simp⟩

lemma isDenseSubsite_inverse_of_isCocontinuous
    [e.functor.IsCocontinuous J K] [e.inverse.IsCocontinuous K J] :
    e.inverse.IsDenseSubsite K J :=
  have : e.symm.functor.IsCocontinuous K J := inferInstanceAs (e.inverse.IsCocontinuous _ _)
  have : e.symm.inverse.IsCocontinuous J K := inferInstanceAs (e.functor.IsCocontinuous _ _)
  isDenseSubsite_functor_of_isCocontinuous _ _ e.symm

variable [e.inverse.IsDenseSubsite K J]

-- INSTANCE (free from Core): :
