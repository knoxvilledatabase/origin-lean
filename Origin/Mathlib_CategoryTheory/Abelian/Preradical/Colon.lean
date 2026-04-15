/-
Extracted from CategoryTheory/Abelian/Preradical/Colon.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The colon construction on preradicals

Given preradicals `Φ` and `Ψ` on an abelian category `C`, this file defines their **colon** `Φ : Ψ`
in the sense of Stenström.  Following Stenström, one can realize the colon object `r : s` evaluated
at `X : C` as the pullback of `X ⟶ X / r X` along `s (X / r X) ⟶ X / r X`. We encode this
categorically by constructing `Φ : Ψ` as a pullback in the category of endofunctors of the canonical
projection `Φ.π : 𝟭 C ⟶ Φ.quotient` along
`Φ.quotient.whiskerLeft Ψ.ι ≫ Φ.quotient.rightUnitor.hom : Φ.quotient ⋙ Ψ.r ⟶ Φ.quotient`.

## Main definitions

* `Preradical.colon Φ Ψ : Preradical C` : The colon preradical `Φ : Ψ` of Stenström.
* `toColon Φ Ψ : Φ ⟶ Φ.colon Ψ` : The canonical inclusion of the left preradical into the colon.

## Main results

* `isIso_toColon_iff` : The morphism `toColon Φ Ψ` is an isomorphism if and only if `Ψ` kills
quotients in the sense that `Φ.quotient ⋙ Ψ.r` is the zero object.

## References

* [Bo Stenström, Rings and Modules of Quotients][stenstrom1971]
* [Bo Stenström, *Rings of Quotients*][stenstrom1975]

## Tags

category_theory, preradical, colon, pullback, torsion theory
-/

namespace CategoryTheory.Abelian

open CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]

namespace Preradical

variable (Φ Ψ : Preradical C)

noncomputable abbrev quotient : C ⥤ C := cokernel Φ.ι

noncomputable def π : 𝟭 C ⟶ Φ.quotient := cokernel.π Φ.ι
  deriving Epi
