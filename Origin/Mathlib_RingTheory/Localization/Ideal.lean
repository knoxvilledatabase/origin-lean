/-
Extracted from RingTheory/Localization/Ideal.lean
Genuine: 8 of 8 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ideals in localizations of commutative rings

## Implementation notes
See `Mathlib/RingTheory/Localization/Basic.lean` for a design overview.

## TODO
Restate the file in terms of `Ideal.under`.

## Tags
localization, ring localization, commutative ring localization, characteristic predicate,
commutative ring, field of fractions

-/

namespace IsLocalization

section CommSemiring

variable {R : Type*} [CommSemiring R] (M : Submonoid R) (S : Type*) [CommSemiring S]

variable [Algebra R S] [IsLocalization M S]

variable {M S} in

theorem mk'_mem_iff {x} {y : M} {I : Ideal S} : mk' S x y ∈ I ↔ algebraMap R S x ∈ I := by
  constructor <;> intro h
  · rw [← mk'_spec S x y, mul_comm]
    exact I.mul_mem_left ((algebraMap R S) y) h
  · rw [← mk'_spec S x y] at h
    obtain ⟨b, hb⟩ := isUnit_iff_exists_inv.1 (map_units S y)
    have := I.mul_mem_left b h
    rwa [mul_comm, mul_assoc, hb, mul_one] at this

private def map_ideal (I : Ideal R) : Ideal S where
  carrier := { z : S | ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 }
  zero_mem' := ⟨⟨0, 1⟩, by simp⟩
  add_mem' := by
    rintro a b ⟨a', ha⟩ ⟨b', hb⟩
    let Z : { x // x ∈ I } := ⟨(a'.2 : R) * (b'.1 : R) + (b'.2 : R) * (a'.1 : R),
      I.add_mem (I.mul_mem_left _ b'.1.2) (I.mul_mem_left _ a'.1.2)⟩
    use ⟨Z, a'.2 * b'.2⟩
    simp only [Z, map_add, Submonoid.coe_mul, map_mul]
    rw [add_mul, ← mul_assoc a, ha, mul_comm (algebraMap R S a'.2) (algebraMap R S b'.2), ←
      mul_assoc b, hb]
    ring
  smul_mem' := by
    rintro c x ⟨x', hx⟩
    obtain ⟨c', hc⟩ := IsLocalization.surj M c
    let Z : { x // x ∈ I } := ⟨c'.1 * x'.1, I.mul_mem_left c'.1 x'.1.2⟩
    use ⟨Z, c'.2 * x'.2⟩
    simp only [Z, ← hx, ← hc, smul_eq_mul, Submonoid.coe_mul, map_mul]
    ring

theorem mem_map_algebraMap_iff {I : Ideal R} {z} : z ∈ Ideal.map (algebraMap R S) I ↔
    ∃ x : I × M, z * algebraMap R S x.2 = algebraMap R S x.1 := by
  constructor
  · change _ → z ∈ map_ideal M S I
    refine fun h => Ideal.mem_sInf.1 h fun z hz => ?_
    obtain ⟨y, hy⟩ := hz
    let Z : { x // x ∈ I } := ⟨y, hy.left⟩
    use ⟨Z, 1⟩
    simp [Z, hy.right]
  · rintro ⟨⟨a, s⟩, h⟩
    rw [← Ideal.unit_mul_mem_iff_mem _ (map_units S s), mul_comm]
    exact h.symm ▸ Ideal.mem_map_of_mem _ a.2

lemma mk'_mem_map_algebraMap_iff (I : Ideal R) (x : R) (s : M) :
    IsLocalization.mk' S x s ∈ I.map (algebraMap R S) ↔ ∃ s ∈ M, s * x ∈ I := by
  rw [← Ideal.unit_mul_mem_iff_mem _ (IsLocalization.map_units S s), IsLocalization.mk'_spec',
    IsLocalization.mem_map_algebraMap_iff M]
  simp_rw [← map_mul, IsLocalization.eq_iff_exists M, mul_comm x, ← mul_assoc, ← Submonoid.coe_mul]
  exact ⟨fun ⟨⟨y, t⟩, c, h⟩ ↦ ⟨_, (c * t).2, h ▸ I.mul_mem_left c.1 y.2⟩, fun ⟨s, hs, h⟩ ↦
    ⟨⟨⟨_, h⟩, ⟨s, hs⟩⟩, 1, by simp⟩⟩

lemma algebraMap_mem_map_algebraMap_iff (I : Ideal R) (x : R) :
    algebraMap R S x ∈ I.map (algebraMap R S) ↔
      ∃ m ∈ M, m * x ∈ I := by
  rw [← IsLocalization.mk'_one (M := M), mk'_mem_map_algebraMap_iff]

lemma map_algebraMap_ne_top_iff_disjoint (I : Ideal R) :
    I.map (algebraMap R S) ≠ ⊤ ↔ Disjoint (M : Set R) (I : Set R) := by
  simp only [ne_eq, Ideal.eq_top_iff_one, ← map_one (algebraMap R S), not_iff_comm,
    IsLocalization.algebraMap_mem_map_algebraMap_iff M]
  simp [Set.disjoint_left]

include M in

protected theorem map_inf (I J : Ideal R) :
    (I ⊓ J).map (algebraMap R S) = I.map (algebraMap R S) ⊓ J.map (algebraMap R S) := by
  refine le_antisymm (Ideal.map_inf_le (algebraMap R S)) fun x hx ↦ ?_
  simp only [Ideal.mem_inf, IsLocalization.mem_map_algebraMap_iff M, Prod.exists] at hx ⊢
  obtain ⟨⟨⟨i, hi⟩, mi, hi'⟩, ⟨j, hj⟩, mj, hj'⟩ := hx
  simp only [← IsLocalization.eq_mk'_iff_mul_eq] at hi' hj'
  obtain ⟨m, hm⟩ := IsLocalization.eq.mp (hi'.symm.trans hj')
  rw [← mul_assoc, ← mul_assoc, mul_comm, ← mul_comm (j : R)] at hm
  refine ⟨⟨i * (m * mj : M), I.mul_mem_right _ hi, hm ▸ J.mul_mem_right _ hj⟩, mi * (m * mj), ?_⟩
  rwa [← IsLocalization.eq_mk'_iff_mul_eq, Subtype.coe_mk, IsLocalization.mk'_cancel]

def mapFrameHom : FrameHom (Ideal R) (Ideal S) where
  toFun := Ideal.map (algebraMap R S)
  map_inf' := IsLocalization.map_inf M S
  map_top' := Ideal.map_top (algebraMap R S)
  map_sSup' _ := (Ideal.gc_map_comap (algebraMap R S)).l_sSup.trans sSup_image.symm
