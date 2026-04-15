/-
Extracted from CategoryTheory/Adjunction/Unique.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Uniqueness of adjoints

This file shows that adjoints are unique up to natural isomorphism.

## Main results

* `Adjunction.leftAdjointUniq` : If `F` and `F'` are both left adjoint to `G`, then they are
  naturally isomorphic.

* `Adjunction.rightAdjointUniq` : If `G` and `G'` are both right adjoint to `F`, then they are
  naturally isomorphic.

-/

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]

namespace CategoryTheory.Adjunction

attribute [local simp] homEquiv_unit homEquiv_counit

def leftAdjointUniq {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G) : F ≅ F' :=
  ((conjugateIsoEquiv adj1 adj2).symm (Iso.refl G)).symm

theorem homEquiv_leftAdjointUniq_hom_app {F F' : C ⥤ D} {G : D ⥤ C} (adj1 : F ⊣ G) (adj2 : F' ⊣ G)
    (x : C) : adj1.homEquiv _ _ ((leftAdjointUniq adj1 adj2).hom.app x) = adj2.unit.app x := by
  simp [leftAdjointUniq]
