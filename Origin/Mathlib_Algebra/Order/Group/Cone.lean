/-
Extracted from Algebra/Order/Group/Cone.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Construct ordered groups from groups with a specified positive cone.

In this file we provide the structure `GroupCone` and the predicate `IsMaxCone`
that encode axioms of `OrderedCommGroup` and `LinearOrderedCommGroup`
in terms of the subset of non-negative elements.

We also provide constructors that convert between
cones in groups and the corresponding ordered groups.
-/

class AddGroupConeClass (S : Type*) (G : outParam Type*) [AddCommGroup G] [SetLike S G] : Prop
    extends AddSubmonoidClass S G where
  eq_zero_of_mem_of_neg_mem {C : S} {a : G} : a ∈ C → -a ∈ C → a = 0
