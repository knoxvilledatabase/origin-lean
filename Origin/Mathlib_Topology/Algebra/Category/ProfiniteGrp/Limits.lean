/-
Extracted from Topology/Algebra/Category/ProfiniteGrp/Limits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# A profinite group is the projective limit of finite groups

We define the topological group isomorphism between a profinite group and the projective limit of
its quotients by open normal subgroups.

## Main definitions

* `toFiniteQuotientFunctor` : The functor from `OpenNormalSubgroup P` to `FiniteGrp`
  sending an open normal subgroup `U` to `P ⧸ U`, where `P : ProfiniteGrp`.

* `toLimit` : The continuous homomorphism from a profinite group `P` to
  the projective limit of its quotients by open normal subgroups ordered by inclusion.

* `ContinuousMulEquivLimittoFiniteQuotientFunctor` : The `toLimit` is a
  `ContinuousMulEquiv`

## Main Statements

* `OpenNormalSubgroupSubClopenNhdsOfOne` : For any open neighborhood of `1` there is an
  open normal subgroup contained in it.

-/

universe u

open CategoryTheory IsTopologicalGroup

namespace ProfiniteGrp

def toFiniteQuotientFunctor (P : ProfiniteGrp) : OpenNormalSubgroup P ⥤ FiniteGrp where
  obj := fun H => FiniteGrp.of (P ⧸ H.toSubgroup)
  map := fun fHK => FiniteGrp.ofHom (QuotientGroup.map _ _ (.id _) (leOfHom fHK))
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <| (QuotientGroup.map_comp_map
    _ _ _ (.id _) (.id _) (leOfHom f) (leOfHom g)).symm
