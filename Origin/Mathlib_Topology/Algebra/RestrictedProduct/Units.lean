/-
Extracted from Topology/Algebra/RestrictedProduct/Units.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Units of restricted products

This file contains results about the units of a restricted product. The restricted
product `Πʳ i : ι, [R i, B i]_[𝓕]` of a family of types `R` with respect to a family of
subsets `B` along a filter `𝓕` is defined in `Mathlib.Topology.Algebra.RestrictedProduct.Basic`.
Here, we give conditions that characterize when an element of the restricted product is a unit,
and provide an isomorphism between the units of the restricted product and the restricted product
of the units.

## Main definitions

* `RestrictedProduct.unitsEquiv`: the (monoid) isomorphism between `(Πʳ i, [R i, B i]_[𝓕])ˣ`
  and `Πʳ i, [(R i)ˣ, (B i).units]_[𝓕]`.

## Tags

restricted product, adeles, ideles
-/

namespace RestrictedProduct

variable {ι : Type*}

variable {R : ι → Type*} [∀ i, Monoid (R i)]

variable {S : ι → Type*} [Π i, SetLike (S i) (R i)] [∀ (i : ι), SubmonoidClass (S i) (R i)]

variable {B : Π i, S i}

variable {𝓕 : Filter ι}

theorem isUnit_of_eventually_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : ∀ i, IsUnit (x i))
    (hxr : ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i)) :
    IsUnit x := by
  rw [isUnit_iff_exists]
  use .mk (fun i ↦ (hx i).unit.inv) (by
    filter_upwards [hxr] with i ⟨h, hu⟩
    have hu : (hx i).unit.1 * hu.unit.inv = 1 := Subtype.val_inj.2 hu.mul_val_inv
    simp [← Units.eq_inv_of_mul_eq_one_left hu])
  simp [RestrictedProduct.ext_iff]

theorem eventually_isUnit_of_isUnit {x : Πʳ i, [R i, B i]_[𝓕]} (hx : IsUnit x) :
    (∀ i, IsUnit (x i)) ∧ ∀ᶠ i in 𝓕, ∃ (h : x i ∈ B i), IsUnit (⟨x i, h⟩ : B i) := by
  simp only [isUnit_iff_exists, RestrictedProduct.ext_iff, ← forall_and] at hx
  simp only [isUnit_iff_exists]
  choose b hb using hx
  exact ⟨Classical.skolem.symm.1 ⟨b, hb⟩, by filter_upwards [x.2, b.2] using
    fun i hx hb ↦ ⟨hx, ⟨b i, hb⟩, by simp_all [← SetLike.coe_eq_coe]⟩⟩
