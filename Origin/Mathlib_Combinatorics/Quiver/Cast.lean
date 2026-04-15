/-
Extracted from Combinatorics/Quiver/Cast.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# Rewriting arrows and paths along vertex equalities

This file defines `Hom.cast` and `Path.cast` (and associated lemmas) in order to allow
rewriting arrows and paths along equalities of their endpoints.

-/

universe v v₁ v₂ u u₁ u₂

variable {U : Type*} [Quiver.{u} U]

namespace Quiver

/-!
### Rewriting arrows along equalities of vertices
-/

def Hom.cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) : u' ⟶ v' :=
  Eq.ndrec (motive := (· ⟶ v')) (Eq.ndrec e hv) hu

theorem Hom.cast_eq_cast {u v u' v' : U} (hu : u = u') (hv : v = v') (e : u ⟶ v) :
    e.cast hu hv = _root_.cast (by {rw [hu, hv]}) e := by
  subst_vars
  rfl
