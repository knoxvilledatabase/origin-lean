/-
Extracted from AlgebraicTopology/FundamentalGroupoid/Product.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Fundamental groupoid preserves products
In this file, we give the following definitions/theorems:

  - `FundamentalGroupoidFunctor.piIso` An isomorphism between Π i, (π Xᵢ) and π (Πi, Xᵢ), whose
    inverse is precisely the product of the maps π (Π i, Xᵢ) → π (Xᵢ), each induced by
    the projection in `Top` Π i, Xᵢ → Xᵢ.

  - `FundamentalGroupoidFunctor.prodIso` An isomorphism between πX × πY and π (X × Y), whose
    inverse is precisely the product of the maps π (X × Y) → πX and π (X × Y) → Y, each induced by
    the projections X × Y → X and X × Y → Y

  - `FundamentalGroupoidFunctor.preservesProduct` A proof that the fundamental groupoid functor
    preserves all products.
-/

noncomputable section

open scoped FundamentalGroupoid CategoryTheory

namespace FundamentalGroupoidFunctor

universe u v

section Pi

variable {I : Type u} (X : I → TopCat.{u})

def proj (i : I) : πₓ (TopCat.of (∀ i, X i)) ⥤ πₓ (X i) :=
  πₘ (TopCat.ofHom ⟨_, continuous_apply i⟩)
