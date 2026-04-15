/-
Extracted from Algebra/Group/Subgroup/Order.lean
Genuine: 8 | Conflates: 0 | Dissolved: 0 | Infrastructure: 5
-/
import Origin.Core
import Mathlib.Order.Atoms
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Algebra.Group.Subsemigroup.Operations
import Mathlib.Algebra.Order.Group.InjSurj
import Mathlib.Algebra.Order.Group.Unbundled.Abs

/-!
# Facts about ordered structures and ordered instances on subgroups
-/

open Subgroup

@[to_additive (attr := simp)]
theorem mabs_mem_iff {S G} [Group G] [LinearOrder G] {_ : SetLike S G}
    [InvMemClass S G] {H : S} {x : G} : |x|ₘ ∈ H ↔ x ∈ H := by
  cases mabs_choice x <;> simp [*]

section ModularLattice

variable {C : Type*} [CommGroup C]

@[to_additive]
instance : IsModularLattice (Subgroup C) :=
  ⟨fun {x} y z xz a ha => by
    rw [mem_inf, mem_sup] at ha
    rcases ha with ⟨⟨b, hb, c, hc, rfl⟩, haz⟩
    rw [mem_sup]
    exact ⟨b, hb, c, mem_inf.2 ⟨hc, (mul_mem_cancel_left (xz hb)).1 haz⟩, rfl⟩⟩

end ModularLattice

section Coatom

namespace Subgroup

variable {G : Type*} [Group G] (H : Subgroup G)

theorem NormalizerCondition.normal_of_coatom (hnc : NormalizerCondition G) (hmax : IsCoatom H) :
    H.Normal :=
  normalizer_eq_top.mp (hmax.2 _ (hnc H (lt_top_iff_ne_top.mpr hmax.1)))

@[simp]
theorem isCoatom_comap {H : Type*} [Group H] (f : G ≃* H) {K : Subgroup H} :
    IsCoatom (Subgroup.comap (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.comapSubgroup) K

@[simp]
theorem isCoatom_map (f : G ≃* H) {K : Subgroup G} :
    IsCoatom (Subgroup.map (f : G →* H) K) ↔ IsCoatom K :=
  OrderIso.isCoatom_iff (f.mapSubgroup) K

lemma isCoatom_comap_of_surjective
    {H : Type*} [Group H] {φ : G →* H} (hφ : Function.Surjective φ)
    {M : Subgroup H} (hM : IsCoatom M) : IsCoatom (M.comap φ) := by
  refine And.imp (fun hM ↦ ?_) (fun hM ↦ ?_) hM
  · rwa [← (comap_injective hφ).ne_iff, comap_top] at hM
  · intro K hK
    specialize hM (K.map φ)
    rw [← comap_lt_comap_of_surjective hφ, ← (comap_injective hφ).eq_iff] at hM
    rw [comap_map_eq_self ((M.ker_le_comap φ).trans hK.le), comap_top] at hM
    exact hM hK

end Subgroup

end Coatom

namespace SubgroupClass

variable {G S : Type*} [SetLike S G]

@[to_additive "An additive subgroup of an `AddOrderedCommGroup` is an `AddOrderedCommGroup`."]
instance (priority := 75) toOrderedCommGroup [OrderedCommGroup G]
    [SubgroupClass S G] (H : S) : OrderedCommGroup H :=
  Subtype.coe_injective.orderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive
      "An additive subgroup of a `LinearOrderedAddCommGroup` is a
        `LinearOrderedAddCommGroup`."]
instance (priority := 75) toLinearOrderedCommGroup [LinearOrderedCommGroup G]
    [SubgroupClass S G] (H : S) : LinearOrderedCommGroup H :=
  Subtype.coe_injective.linearOrderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end SubgroupClass

namespace Subgroup

variable {G : Type*}

@[to_additive "An `AddSubgroup` of an `AddOrderedCommGroup` is an `AddOrderedCommGroup`."]
instance toOrderedCommGroup [OrderedCommGroup G] (H : Subgroup G) :
    OrderedCommGroup H :=
  Subtype.coe_injective.orderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) fun _ _ => rfl

@[to_additive
      "An `AddSubgroup` of a `LinearOrderedAddCommGroup` is a
        `LinearOrderedAddCommGroup`."]
instance toLinearOrderedCommGroup [LinearOrderedCommGroup G] (H : Subgroup G) :
    LinearOrderedCommGroup H :=
  Subtype.coe_injective.linearOrderedCommGroup _ rfl (fun _ _ => rfl) (fun _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) fun _ _ => rfl

end Subgroup

@[to_additive]
lemma Subsemigroup.strictMono_topEquiv {G : Type*} [OrderedCommMonoid G] :
    StrictMono (topEquiv (M := G)) := fun _ _ ↦ id

@[to_additive]
lemma MulEquiv.strictMono_subsemigroupCongr {G : Type*} [OrderedCommMonoid G] {S T : Subsemigroup G}
    (h : S = T) : StrictMono (subsemigroupCongr h) := fun _ _ ↦ id

@[to_additive]
lemma MulEquiv.strictMono_symm {G G' : Type*} [LinearOrderedCommMonoid G]
    [LinearOrderedCommMonoid G'] {e : G ≃* G'} (he : StrictMono e) : StrictMono e.symm := by
  intro
  simp [← he.lt_iff_lt]
