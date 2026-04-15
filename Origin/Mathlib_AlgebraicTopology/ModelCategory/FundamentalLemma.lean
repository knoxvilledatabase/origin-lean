/-
Extracted from AlgebraicTopology/ModelCategory/FundamentalLemma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The fundamental lemma of homotopical algebra

Let `C` be a model category. Let `L : C ⥤ H` be a localization functor
with respect to weak equivalences in `C`. We obtain the fundamental
lemma of homotopical algebra: if `X` is cofibrant and `Y` fibrant,
the map `(X ⟶ Y) → (L.obj X ⟶ L.obj Y)` identifies `L.obj X ⟶ L.obj Y`
to the quotient of `X ⟶ Y` by the homotopy relation (in this case,
the left and right homotopy relations coincide).

## References
* [Daniel G. Quillen, Homotopical algebra, I.1][Quillen1967]

-/

open CategoryTheory Limits

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C] {H : Type*} [Category* H]
  (L : C ⥤ H) [L.IsLocalization (weakEquivalences _)]
  {X Y : C}

def leftHomotopyClassToHom : LeftHomotopyClass X Y → (L.obj X ⟶ L.obj Y) :=
  Quot.lift L.map (fun _ _ h ↦ h.factorsThroughLocalization.map_eq _)
