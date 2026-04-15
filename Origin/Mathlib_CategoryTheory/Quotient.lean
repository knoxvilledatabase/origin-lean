/-
Extracted from CategoryTheory/Quotient.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Quotient category

Constructs the quotient of a category by an arbitrary family of relations on its hom-sets,
by introducing a type synonym for the objects, and identifying homs as necessary.

This is analogous to 'the quotient of a group by the normal closure of a subset', rather
than 'the quotient of a group by a normal subgroup'. When taking the quotient by a congruence
relation, `functor_map_eq_iff` says that no unnecessary identifications have been made.
-/

def HomRel (C) [Quiver C] :=
  ∀ ⦃X Y : C⦄, (X ⟶ Y) → (X ⟶ Y) → Prop

deriving Inhabited

namespace CategoryTheory

open Functor

variable {C D : Type*} [Category* C] [Category* D] (F : C ⥤ D)

def Functor.homRel : HomRel C :=
  fun _ _ f g ↦ F.map f = F.map g
