/-
Extracted from AlgebraicGeometry/Sites/BigZariski.lean
Genuine: 3 of 5 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# The big Zariski site of schemes

In this file, we define the Zariski topology, as a Grothendieck topology on the
category `Scheme.{u}`: this is `Scheme.zariskiTopology.{u}`. If `X : Scheme.{u}`,
the Zariski topology on `Over X` can be obtained as `Scheme.zariskiTopology.over X`
(see `CategoryTheory.Sites.Over`.).

TODO:
* If `Y : Scheme.{u}`, define a continuous functor from the category of opens of `Y`
  to `Over Y`, and show that a presheaf on `Over Y` is a sheaf for the Zariski topology
  iff its "restriction" to the topological space `Z` is a sheaf for all `Z : Over Y`.
* We should have good notions of (pre)sheaves of `Type (u + 1)` (e.g. associated
  sheaf functor, pushforward, pullbacks) on `Scheme.{u}` for this topology. However,
  some constructions in the `CategoryTheory.Sites` folder currently assume that
  the site is a small category: this should be generalized. As a result,
  this big Zariski site can considered as a test case of the Grothendieck topology API
  for future applications to étale cohomology.

-/

universe v u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

def zariskiPretopology : Pretopology Scheme.{u} :=
  pretopology @IsOpenImmersion

abbrev zariskiTopology : GrothendieckTopology Scheme.{u} :=
  grothendieckTopology IsOpenImmersion

lemma zariskiTopology_eq : zariskiTopology.{u} = zariskiPretopology.toGrothendieck :=
  Precoverage.toGrothendieck_toPretopology_eq_toGrothendieck.symm

-- INSTANCE (free from Core): subcanonical_zariskiTopology

-- INSTANCE (free from Core): :
