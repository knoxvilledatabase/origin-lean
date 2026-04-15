/-
Extracted from GroupTheory/PresentedGroup.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Defining a group given by generators and relations

Given a subset `rels` of relations of the free group on a type `α`, this file constructs the group
given by generators `x : α` and relations `r ∈ rels`.

## Main definitions

* `PresentedGroup rels`: the quotient group of the free group on a type `α` by a subset `rels` of
  relations of the free group on `α`.
* `of`: The canonical map from `α` to a presented group with generators `α`.
* `toGroup f`: the canonical group homomorphism `PresentedGroup rels → G`, given a function
  `f : α → G` from a type `α` to a group `G` which satisfies the relations `rels`.

## Tags

generators, relations, group presentations
-/

variable {α : Type*}

def PresentedGroup (rels : Set (FreeGroup α)) :=
  FreeGroup α ⧸ Subgroup.normalClosure rels

deriving Group

namespace PresentedGroup

def mk (rels : Set (FreeGroup α)) : FreeGroup α →* PresentedGroup rels :=
  ⟨⟨QuotientGroup.mk, rfl⟩, fun _ _ => rfl⟩

theorem mk_surjective (rels : Set (FreeGroup α)) : Function.Surjective <| mk rels :=
  QuotientGroup.mk_surjective

def of {rels : Set (FreeGroup α)} (x : α) : PresentedGroup rels :=
  mk rels (FreeGroup.of x)

lemma mk_eq_one_iff {rels : Set (FreeGroup α)} {x : FreeGroup α} :
    mk rels x = 1 ↔ x ∈ Subgroup.normalClosure rels :=
  QuotientGroup.eq_one_iff _

lemma one_of_mem {rels : Set (FreeGroup α)} {x : FreeGroup α} (hx : x ∈ rels) :
    mk rels x = 1 :=
  mk_eq_one_iff.mpr <| Subgroup.subset_normalClosure hx

lemma mk_eq_mk_of_mul_inv_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x * y⁻¹ ∈ rels) : mk rels x = mk rels y :=
  eq_of_mul_inv_eq_one <| one_of_mem hx

lemma mk_eq_mk_of_inv_mul_mem {rels : Set (FreeGroup α)} {x y : FreeGroup α}
    (hx : x⁻¹ * y ∈ rels) : mk rels x = mk rels y :=
  eq_of_inv_mul_eq_one <| one_of_mem hx

set_option backward.isDefEq.respectTransparency false in
