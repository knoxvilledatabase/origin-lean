/-
Extracted from AlgebraicTopology/ModelCategory/BrownLemma.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The factorization lemma by K. S. Brown

In a model category, any morphism `f : X ⟶ Y` between
cofibrant objects can be factored as `i ≫ p`
with `i` a cofibration and `p` a trivial fibration
which has a section `s` that is a cofibration.
In order to state this, we introduce a structure
`CofibrantBrownFactorization f` with the data
of such morphisms `i`, `p` and `s` with the expected
properties, and show it is nonempty.
Moreover, if `f` is a weak equivalence, then all the
morphisms `i`, `p` and `s` are weak equivalences.
(We also obtain the dual results about morphisms
between fibrant objects.)

## References
* [Brown, Kenneth S., *Abstract homotopy theory and generalized sheaf cohomology*, §I.1][brown-1973]

-/

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra

variable {C : Type*} [Category* C] [ModelCategory C]
  {X Y : C} (f : X ⟶ Y)

structure CofibrantBrownFactorization extends
    MapFactorizationData (cofibrations C) (trivialFibrations C) f where
  /-- a cofibration that is a section of `p` -/
  s : Y ⟶ Z
  s_p : s ≫ p = 𝟙 Y := by cat_disch
  cofibration_s : Cofibration s := by infer_instance

namespace CofibrantBrownFactorization

attribute [reassoc (attr := simp)] s_p

attribute [instance] cofibration_s

variable (h : CofibrantBrownFactorization f)

-- INSTANCE (free from Core): [WeakEquivalence

-- INSTANCE (free from Core): :

set_option backward.isDefEq.respectTransparency false in
