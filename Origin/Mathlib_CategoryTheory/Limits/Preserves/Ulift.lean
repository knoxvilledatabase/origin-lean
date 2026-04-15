/-
Extracted from CategoryTheory/Limits/Preserves/Ulift.lean
Genuine: 1 of 5 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# `ULift` creates small (co)limits


This file shows that `uliftFunctor.{v, u}` preserves all limits and colimits, including those
potentially too big to exist in `Type u`.

As this functor is fully faithful, we also deduce that it creates `u`-small limits and
colimits.

-/

universe v w w' u

namespace CategoryTheory.Limits.Types

set_option backward.isDefEq.respectTransparency false in

def sectionsEquiv {J : Type*} [Category* J] (K : J ⥤ Type u) :
    K.sections ≃ (K ⋙ uliftFunctor.{v, u}).sections where
  toFun := fun ⟨u, hu⟩ => ⟨fun j => ⟨u j⟩, fun f => by simp [hu f]⟩
  invFun := fun ⟨u, hu⟩ => ⟨fun j => (u j).down, @fun j j' f => by simp [← hu f]⟩

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

variable {J : Type*} [Category* J] {K : J ⥤ Type u} {c : Cocone K} (hc : IsColimit c)

variable {lc : Cocone (K ⋙ uliftFunctor.{v, u})}

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

end CategoryTheory.Limits.Types
