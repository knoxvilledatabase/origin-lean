/-
Extracted from GroupTheory/ResiduallyFinite.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Residually Finite Groups

In this file we define residually finite groups and prove some basic properties.

## Main definitions

- `Group.ResiduallyFinite G`: A group `G` is residually finite if the intersection of all
  finite index normal subgroups is trivial.

-/

class AddGroup.ResiduallyFinite (G : Type*) [AddGroup G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalAddSubgroup G, H.toAddSubgroup = ⊥

namespace Group

class ResiduallyFinite (G : Type*) [Group G] : Prop where
  iInf_eq_bot : ⨅ H : FiniteIndexNormalSubgroup G, H.toSubgroup = ⊥

attribute [to_additive existing] ResiduallyFinite

variable {G : Type*} [Group G]
