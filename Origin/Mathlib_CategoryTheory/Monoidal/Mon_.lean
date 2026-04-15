/-
Extracted from CategoryTheory/Monoidal/Mon_.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The category of monoids in a monoidal category.

We define monoids in a monoidal category `C` and show that the category of monoids is equivalent to
the category of lax monoidal functors from the unit monoidal category to `C`.  We also show that if
`C` is braided, then the category of monoids is naturally monoidal.
We use the `to_additive` attribute in order to generate a parallel API for additive monoids.

## Simp set for monoid object tautologies

In this file, we also provide a simp set called `mon_tauto` whose goal is to prove all tautologies
about morphisms from some (tensor) power of `M` to `M`, where `M` is a (commutative) monoid object
in a (braided) monoidal category.

Please read the documentation in `Mathlib/Tactic/Attr/Register.lean` for full details.

## TODO

* Check that `Mon MonCat ≌ CommMonCat`, via the Eckmann-Hilton argument.
  (You'll have to hook up the Cartesian monoidal structure on `MonCat` first,
  available in https://github.com/leanprover-community/mathlib3/pull/3463)
* More generally, check that `Mon (Mon C) ≌ CommMon C` when `C` is braided.
* Check that `Mon TopCat ≌ [bundled topological monoids]`.
* Check that `Mon AddCommGrpCat ≌ RingCat`.
  (We've already got `Mon (ModuleCat R) ≌ AlgCat R`,
  in `Mathlib/CategoryTheory/Monoidal/Internal/Module.lean`.)
* Can you transport this monoidal structure to `RingCat` or `AlgCat R`?
  How does it compare to the "native" one?
-/

universe w v₁ v₂ v₃ u₁ u₂ u₃ u

open Function CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory.{v₁} C]

class AddMonObj (X : C) where
  /-- The zero morphism of an additive monoid object. -/
  zero : 𝟙_ C ⟶ X
  /-- The addition morphism of an additive monoid object. -/
  add : X ⊗ X ⟶ X
  zero_add (X) : zero ▷ X ≫ add = (λ_ X).hom := by cat_disch
  add_zero (X) : X ◁ zero ≫ add = (ρ_ X).hom := by cat_disch
  -- Obviously there is some flexibility stating this axiom.
  -- This one has left- and right-hand sides matching the statement of `_root_.add_assoc`,
  -- and chooses to place the associator on the right-hand side.
  -- The heuristic is that unitors and associators "don't have much weight".
  add_assoc (X) : (add ▷ X) ≫ add = (α_ X X X).hom ≫ (X ◁ add) ≫ add := by cat_disch
