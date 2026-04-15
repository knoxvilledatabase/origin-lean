/-
Extracted from CategoryTheory/Abelian/Preradical/Basic.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Preradicals

A **preradical** on an abelian category `C` is a monomorphism in the functor category `C ⥤ C`
with codomain `𝟭 C`, i.e. an element of `MonoOver (𝟭 C)`.

## Main definitions

* `Preradical C`: The type of preradicals on `C`.
* `Preradical.r`: The underlying endofunctor of a `Preradical`.
* `Preradical.ι`: The structure morphism of a `Preradical`.
* `Preradical.IsIdempotent`: The predicate expressing idempotence.

## References

* [Bo Stenström, *Rings and Modules of Quotients*][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category theory, preradical, torsion theory
-/

universe v u

namespace CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C]

variable (C) in

abbrev Preradical := MonoOver (𝟭 C)

namespace Preradical

variable (Φ : Preradical C)

abbrev r : C ⥤ C := Φ.obj.left

abbrev ι : Φ.r ⟶ 𝟭 C := Φ.obj.hom

set_option backward.isDefEq.respectTransparency false in
