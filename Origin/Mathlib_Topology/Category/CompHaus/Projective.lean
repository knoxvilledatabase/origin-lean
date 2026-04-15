/-
Extracted from Topology/Category/CompHaus/Projective.lean
Genuine: 1 of 3 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# CompHaus has enough projectives

In this file we show that `CompHaus` has enough projectives.

## Main results

Let `X` be a compact Hausdorff space.

* `CompHaus.projective_ultrafilter`: the space `Ultrafilter X` is a projective object
* `CompHaus.projectivePresentation`: the natural map `Ultrafilter X → X`
  is a projective presentation

## Reference

See [miraglia2006introduction] Chapter 21 for a proof that `CompHaus` has enough projectives.

-/

noncomputable section

open CategoryTheory Function

namespace CompHaus

-- INSTANCE (free from Core): projective_ultrafilter

def projectivePresentation (X : CompHaus) : ProjectivePresentation X where
  p := of <| Ultrafilter X
  f := CompHausLike.ofHom _ ⟨_, continuous_ultrafilter_extend id⟩
  projective := CompHaus.projective_ultrafilter X
  epi :=
    ConcreteCategory.epi_of_surjective _ fun x =>
      ⟨(pure x : Ultrafilter X), congr_fun (ultrafilter_extend_extends (𝟙 X)) x⟩

-- INSTANCE (free from Core): :

end CompHaus
