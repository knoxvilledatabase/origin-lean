/-
Extracted from CategoryTheory/Sites/NonabelianCohomology/H1.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-! The cohomology of a sheaf of groups in degree 1

In this file, we shall define the cohomology in degree 1 of a sheaf
of groups (TODO).

Currently, given a presheaf of groups `G : Cᵒᵖ ⥤ GrpCat` and a family
of objects `U : I → C`, we define 1-cochains/1-cocycles/H^1 with values
in `G` over `U`. (This definition neither requires the assumption that `G`
is a sheaf, nor that `U` covers the terminal object.)
As we do not assume that `G` is a presheaf of abelian groups, this
cohomology theory is only defined in low degrees; in the abelian
case, it would be a particular case of Čech cohomology (TODO).

## TODO

* show that if `1 ⟶ G₁ ⟶ G₂ ⟶ G₃ ⟶ 1` is a short exact sequence of sheaves
  of groups, and `x₃` is a global section of `G₃` which can be locally lifted
  to a section of `G₂`, there is an associated canonical cohomology class of `G₁`
  which is trivial iff `x₃` can be lifted to a global section of `G₂`.
  (This should hold more generally if `G₂` is a sheaf of sets on which `G₁` acts
  freely, and `G₃` is the quotient sheaf.)
* deduce a similar result for abelian sheaves
* when the notion of quasi-coherent sheaves on schemes is defined, show that
  if `0 ⟶ Q ⟶ M ⟶ N ⟶ 0` is an exact sequence of abelian sheaves over a scheme `X`
  and `Q` is the underlying sheaf of a quasi-coherent sheaf, then `M(U) ⟶ N(U)`
  is surjective for any affine open `U`.
* take the colimit of `OneCohomology G U` over all covering families `U` (for
  a Grothendieck topology)

# References

* [J. Frenkel, *Cohomologie non abélienne et espaces fibrés*][frenkel1957]

-/

universe w' w v u

namespace CategoryTheory

variable {C : Type u} [Category.{v} C]

namespace PresheafOfGroups

variable (G : Cᵒᵖ ⥤ GrpCat.{w}) {I : Type w'} (U : I → C)

def ZeroCochain := ∀ (i : I), G.obj (Opposite.op (U i))

-- INSTANCE (free from Core): :

namespace Cochain₀
