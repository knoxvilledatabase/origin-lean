/-
Extracted from AlgebraicGeometry/Sites/Etale.lean
Genuine: 3 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.BigZariski

/-!

# The étale site

In this file we define the big étale site, i.e. the étale topology as a Grothendieck topology
on the category of schemes.

## TODO:

- define the small étale site

-/

universe v u

open CategoryTheory MorphismProperty Limits

namespace AlgebraicGeometry.Scheme

def etalePretopology : Pretopology Scheme.{u} :=
  pretopology @IsEtale

abbrev etaleTopology : GrothendieckTopology Scheme.{u} :=
  etalePretopology.toGrothendieck

lemma zariskiTopology_le_etaleTopology : zariskiTopology ≤ etaleTopology := by
  apply grothendieckTopology_le_grothendieckTopology
  intro X Y f hf
  infer_instance

end AlgebraicGeometry.Scheme
