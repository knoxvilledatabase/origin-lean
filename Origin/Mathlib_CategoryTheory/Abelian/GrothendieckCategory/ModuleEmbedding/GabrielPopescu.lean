/-
Extracted from CategoryTheory/Abelian/GrothendieckCategory/ModuleEmbedding/GabrielPopescu.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The Gabriel-Popescu theorem

We prove the following Gabriel-Popescu theorem: if `C` is a Grothendieck abelian category and
`G` is a separator, then the functor `preadditiveCoyonedaObj G : C ⥤ ModuleCat (End G)ᵐᵒᵖ` sending
`X` to `Hom(G, X)` is fully faithful and has an exact left adjoint.

We closely follow the elementary proof given by Barry Mitchell.

## Future work

The left adjoint `tensorObj G` actually exists as soon as `C` is cocomplete and additive, so the
construction could be generalized.

The theorem as stated here implies that `C` is a Serre quotient of `ModuleCat (End G)ᵐᵒᵖ`.

## References

* [Barry Mitchell, *A quick proof of the Gabriel-Popesco theorem*][mitchell1981]
-/

universe v u

open CategoryTheory Limits Abelian

namespace CategoryTheory.IsGrothendieckAbelian

variable {C : Type u} [Category.{v} C] [Abelian C] [IsGrothendieckAbelian.{v} C]

-- INSTANCE (free from Core): {G

noncomputable def tensorObj (G : C) : ModuleCat (End G)ᵐᵒᵖ ⥤ C :=
  (preadditiveCoyonedaObj G).leftAdjoint

noncomputable def tensorObjPreadditiveCoyonedaObjAdjunction (G : C) :
    tensorObj G ⊣ preadditiveCoyonedaObj G :=
  Adjunction.ofIsRightAdjoint _

-- INSTANCE (free from Core): {G

namespace GabrielPopescuAux

open CoproductsFromFiniteFiltered

noncomputable def d {G A : C} {M : ModuleCat (End G)ᵐᵒᵖ}
    (g : M ⟶ ModuleCat.of (End G)ᵐᵒᵖ (G ⟶ A)) : ∐ (fun (_ : M) => G) ⟶ A :=
  Sigma.desc fun (m : M) => g m

set_option backward.isDefEq.respectTransparency false in
