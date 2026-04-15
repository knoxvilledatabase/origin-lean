/-
Extracted from CategoryTheory/Comma/Over/OverClass.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Typeclasses for `S`-objects and `S`-morphisms

**Warning**: This is not usually how typeclasses should be used.
This is only a sensible approach when the morphism is considered as a structure on `X`,
typically in algebraic geometry.

This is analogous to how we view ringhoms as structures via the `Algebra` typeclass.

For other applications use unbundled arrows or `CategoryTheory.Over`.

## Main definition
- `CategoryTheory.OverClass`: `OverClass X S` equips `X` with a morphism into `S`.
  `X ↘ S : X ⟶ S` is the structure morphism.
- `CategoryTheory.HomIsOver`:
  `HomIsOver f S` asserts that `f` commutes with the structure morphisms.

-/

namespace CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

variable {X Y Z : C} (f : X ⟶ Y) (S S' : C)

class OverClass (X S : C) : Type v where
  ofHom ::
  /-- The structure morphism. Use `X ↘ S` instead. -/
  hom : X ⟶ S

def over (X S : C) (_ : OverClass X S := by infer_instance) : X ⟶ S := OverClass.hom

notation:90 X:90 " ↘ " S:90 => CategoryTheory.over X S inferInstance

def OverClass.Simps.over (X S : C) [OverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections OverClass (hom → over)

class CanonicallyOverClass (X : C) (S : semiOutParam C) extends OverClass X S where

def CanonicallyOverClass.Simps.over (X S : C) [CanonicallyOverClass X S] : X ⟶ S := X ↘ S

initialize_simps_projections CanonicallyOverClass (hom → over)
