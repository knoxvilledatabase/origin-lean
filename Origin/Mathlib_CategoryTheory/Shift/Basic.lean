/-
Extracted from CategoryTheory/Shift/Basic.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Shift

A `Shift` on a category `C` indexed by a monoid `A` is nothing more than a monoidal functor
from `A` to `C ⥤ C`. A typical example to keep in mind might be the category of
complexes `⋯ → C_{n-1} → C_n → C_{n+1} → ⋯`. It has a shift indexed by `ℤ`, where we assign to
each `n : ℤ` the functor `C ⥤ C` that re-indexes the terms, so the degree `i` term of `Shift n C`
would be the degree `i+n`-th term of `C`.

## Main definitions
* `HasShift`: A typeclass asserting the existence of a shift functor.
* `shiftEquiv`: When the indexing monoid is a group, then the functor indexed by `n` and `-n` forms
  a self-equivalence of `C`.
* `shiftComm`: When the indexing monoid is commutative, then shifts commute as well.

## Implementation Notes

`[HasShift C A]` is implemented using monoidal functors from `Discrete A` to `C ⥤ C`.
However, the API of monoidal functors is used only internally: one should use the API of
shift functors which includes `shiftFunctor C a : C ⥤ C` for `a : A`,
`shiftFunctorZero C A : shiftFunctor C (0 : A) ≅ 𝟭 C` and
`shiftFunctorAdd C i j : shiftFunctor C (i + j) ≅ shiftFunctor C i ⋙ shiftFunctor C j`
(and its variant `shiftFunctorAdd'`). These isomorphisms satisfy some coherence properties
which are stated in lemmas like `shiftFunctorAdd'_assoc`, `shiftFunctorAdd'_zero_add` and
`shiftFunctorAdd'_add_zero`.

-/

namespace CategoryTheory

open Functor

noncomputable section

universe v u

variable (C : Type u) (A : Type*) [Category.{v} C]

attribute [local instance] endofunctorMonoidalCategory

variable {A C}

section Defs

variable (A C) [AddMonoid A]

class HasShift (C : Type u) (A : Type*) [Category.{v} C] [AddMonoid A] where
  /-- a shift is a monoidal functor from `A` to `C ⥤ C` -/
  shift : Discrete A ⥤ C ⥤ C
  /-- `shift` is monoidal -/
  shiftMonoidal : shift.Monoidal := by infer_instance

structure ShiftMkCore where
  /-- the family of shift functors -/
  F : A → C ⥤ C
  /-- the shift by 0 identifies to the identity functor -/
  zero : F 0 ≅ 𝟭 C
  /-- the composition of shift functors identifies to the shift by the sum -/
  add : ∀ n m : A, F (n + m) ≅ F n ⋙ F m
  /-- compatibility with the associativity -/
  assoc_hom_app : ∀ (m₁ m₂ m₃ : A) (X : C),
    (add (m₁ + m₂) m₃).hom.app X ≫ (F m₃).map ((add m₁ m₂).hom.app X) =
      eqToHom (by rw [add_assoc]) ≫ (add m₁ (m₂ + m₃)).hom.app X ≫
        (add m₂ m₃).hom.app ((F m₁).obj X) := by cat_disch
  /-- compatibility with the left addition with 0 -/
  zero_add_hom_app : ∀ (n : A) (X : C), (add 0 n).hom.app X =
    eqToHom (by dsimp; rw [zero_add]) ≫ (F n).map (zero.inv.app X) := by cat_disch
  /-- compatibility with the right addition with 0 -/
  add_zero_hom_app : ∀ (n : A) (X : C), (add n 0).hom.app X =
    eqToHom (by dsimp; rw [add_zero]) ≫ zero.inv.app ((F n).obj X) := by cat_disch

namespace ShiftMkCore

variable {C A}

attribute [reassoc] assoc_hom_app

set_option backward.isDefEq.respectTransparency false in
