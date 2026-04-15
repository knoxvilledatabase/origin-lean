/-
Extracted from RingTheory/Valuation/Integers.lean
Genuine: 33 of 37 | Dissolved: 1 | Infrastructure: 3
-/
import Origin.Core

/-!
# Ring of integers under a given valuation

The elements with valuation less than or equal to 1.

TODO: Define characteristic predicate.
-/

open Set

universe u v w

namespace Valuation

section Ring

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

variable (v : Valuation R Γ₀)

def integer : Subring R where
  carrier := { x | v x ≤ 1 }
  one_mem' := le_of_eq v.map_one
  mul_mem' {x y} hx hy := by simp only [Set.mem_setOf_eq, map_mul, mul_le_one' hx hy]
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero, zero_le']
  add_mem' {x y} hx hy := le_trans (v.map_add x y) (max_le hx hy)
  neg_mem' {x} hx := by simp only [Set.mem_setOf_eq] at hx; simpa only [Set.mem_setOf_eq, map_neg]

end Ring

section CommRing

variable {R : Type u} {Γ₀ : Type v} [CommRing R] [LinearOrderedCommGroupWithZero Γ₀]

variable (v : Valuation R Γ₀)

variable (O : Type w) [CommRing O] [Algebra O R]

structure Integers : Prop where
  hom_inj : Function.Injective (algebraMap O R)
  map_le_one : ∀ x, v (algebraMap O R x) ≤ 1
  exists_of_le_one : ∀ ⦃r⦄, v r ≤ 1 → ∃ x, algebraMap O R x = r

-- INSTANCE (free from Core): :

theorem integer.integers : v.Integers v.integer :=
  { hom_inj := Subtype.coe_injective
    map_le_one := fun r => r.2
    exists_of_le_one := fun r hr => ⟨⟨r, hr⟩, rfl⟩ }

namespace Integers

variable {v O}

theorem one_of_isUnit' {x : O} (hx : IsUnit x) (H : ∀ x, v (algebraMap O R x) ≤ 1) :
    v (algebraMap O R x) = 1 :=
  let ⟨u, hu⟩ := hx
  le_antisymm (H _) <| by
    grw [← v.map_one, ← (algebraMap O R).map_one, ← u.mul_inv, ← mul_one (v (algebraMap O R x)), hu,
      (algebraMap O R).map_mul, v.map_mul, H (u⁻¹ : Units O)]

theorem one_of_isUnit (hv : Integers v O) {x : O} (hx : IsUnit x) : v (algebraMap O R x) = 1 :=
  one_of_isUnit' hx hv.map_le_one

theorem isUnit_of_one (hv : Integers v O) {x : O} (hx : IsUnit (algebraMap O R x))
    (hvx : v (algebraMap O R x) = 1) : IsUnit x :=
  let ⟨u, hu⟩ := hx
  have h1 : v u ≤ 1 := hu.symm ▸ hv.2 x
  have h2 : v (u⁻¹ : Rˣ) ≤ 1 := by
    rw [← one_mul (v _), ← hvx, ← v.map_mul, ← hu, u.mul_inv, hu, hvx, v.map_one]
  let ⟨r1, hr1⟩ := hv.3 h1
  let ⟨r2, hr2⟩ := hv.3 h2
  ⟨⟨r1, r2, hv.1 <| by rw [map_mul, map_one, hr1, hr2, Units.mul_inv],
      hv.1 <| by rw [map_mul, map_one, hr1, hr2, Units.inv_mul]⟩,
    hv.1 <| hr1.trans hu⟩

lemma nontrivial_iff (hv : v.Integers O) : Nontrivial O ↔ Nontrivial R := by
  constructor <;> intro h
  · exact hv.hom_inj.nontrivial
  · obtain ⟨o0, ho0⟩ := hv.exists_of_le_one (r := 0) (by simp)
    obtain ⟨o1, ho1⟩ := hv.exists_of_le_one (r := 1) (by simp)
    refine ⟨o0, o1, ?_⟩
    rintro rfl
    simp [ho1] at ho0

end Integers

theorem IsTrivialOn.of_le_one {k : Type*} [Field k] [Algebra k R] (v : Valuation R Γ₀)
    (hle : ∀ (x : k), v (algebraMap k R x) ≤ 1) : v.IsTrivialOn k where
  eq_one a ha := Valuation.Integers.one_of_isUnit' (IsUnit.mk0 a ha) hle

lemma integers_nontrivial (v : Valuation R Γ₀) :
    Nontrivial v.integer ↔ Nontrivial R :=
  (Valuation.integer.integers v).nontrivial_iff

end CommRing

section Field

variable {F : Type u} {Γ₀ : Type v} [Field F] [LinearOrderedCommGroupWithZero Γ₀]

variable {v : Valuation F Γ₀} {O : Type w} [CommRing O] [Algebra O F]

namespace Integers

theorem dvd_of_le (hv : Integers v O) {x y : O}
    (h : v (algebraMap O F x) ≤ v (algebraMap O F y)) : y ∣ x :=
  by_cases
    (fun hy : algebraMap O F y = 0 =>
      have hx : x = 0 :=
        hv.1 <|
          (algebraMap O F).map_zero.symm ▸ (v.zero_iff.1 <| le_zero_iff.1 (v.map_zero ▸ hy ▸ h))
      hx.symm ▸ dvd_zero y)
    fun hy : algebraMap O F y ≠ 0 =>
    have : v ((algebraMap O F y)⁻¹ * algebraMap O F x) ≤ 1 := by
      grw [← v.map_one, ← inv_mul_cancel₀ hy, v.map_mul, v.map_mul, h]
    let ⟨z, hz⟩ := hv.3 this
    ⟨z, hv.1 <| ((algebraMap O F).map_mul y z).symm ▸ hz.symm ▸ (mul_inv_cancel_left₀ hy _).symm⟩

theorem dvd_iff_le (hv : Integers v O) {x y : O} :
    x ∣ y ↔ v (algebraMap O F y) ≤ v (algebraMap O F x) :=
  ⟨hv.le_of_dvd, hv.dvd_of_le⟩

theorem le_iff_dvd (hv : Integers v O) {x y : O} :
    v (algebraMap O F x) ≤ v (algebraMap O F y) ↔ y ∣ x :=
  ⟨hv.dvd_of_le, hv.le_of_dvd⟩

theorem isUnit_of_one' (hv : Integers v O) {x : O} (hvx : v (algebraMap O F x) = 1) : IsUnit x := by
  refine isUnit_of_one hv (IsUnit.mk0 _ ?_) hvx
  simp only [← v.ne_zero_iff, hvx, ne_eq, one_ne_zero, not_false_eq_true]

lemma isUnit_iff_valuation_eq_one (hv : Integers v O) {x : O} :
    IsUnit x ↔ v (algebraMap O F x) = 1 :=
  ⟨hv.one_of_isUnit, hv.isUnit_of_one'⟩

lemma valuation_irreducible_lt_one (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    v (algebraMap O F ϖ) < 1 :=
  lt_of_le_of_ne (hv.map_le_one ϖ) (mt hv.isUnit_iff_valuation_eq_one.mpr h.not_isUnit)

lemma valuation_unit (hv : Integers v O) (x : Oˣ) :
    v (algebraMap O F x) = 1 := by
  simp [← hv.isUnit_iff_valuation_eq_one]

-- DISSOLVED: valuation_pos_iff_ne_zero

lemma valuation_irreducible_pos (hv : Integers v O) {ϖ : O} (h : Irreducible ϖ) :
    0 < v (algebraMap O F ϖ) :=
  hv.valuation_pos_iff_ne_zero.mpr h.ne_zero

theorem dvdNotUnit_iff_lt (hv : Integers v O) {x y : O} :
    DvdNotUnit x y ↔ v (algebraMap O F y) < v (algebraMap O F x) := by
  rw [lt_iff_le_not_ge, hv.le_iff_dvd, hv.le_iff_dvd]
  refine ⟨?_, And.elim dvdNotUnit_of_dvd_of_not_dvd⟩
  rintro ⟨hx0, d, hdu, rfl⟩
  refine ⟨⟨d, rfl⟩, ?_⟩
  rw [hv.isUnit_iff_valuation_eq_one, ← ne_eq, ne_iff_lt_iff_le.mpr (hv.map_le_one d)] at hdu
  rw [dvd_iff_le hv]
  simp only [map_mul, not_le]
  contrapose! hdu
  refine one_le_of_le_mul_left₀ ?_ hdu
  simp [hv.valuation_pos_iff_ne_zero, hx0]

theorem eq_algebraMap_or_inv_eq_algebraMap (hv : Integers v O) (x : F) :
    ∃ a : O, x = algebraMap O F a ∨ x⁻¹ = algebraMap O F a := by
  rcases val_le_one_or_val_inv_le_one v x with h | h <;>
  obtain ⟨a, ha⟩ := exists_of_le_one hv h
  exacts [⟨a, Or.inl ha.symm⟩, ⟨a, Or.inr ha.symm⟩]

lemma coe_span_singleton_eq_setOf_le_v_algebraMap (hv : Integers v O) (x : O) :
    (Ideal.span {x} : Set O) = {y : O | v (algebraMap O F y) ≤ v (algebraMap O F x)} := by
  rcases eq_or_ne x 0 with rfl | hx
  · simp [Set.singleton_zero, Ideal.span_zero, map_eq_zero_iff _ hv.hom_inj]
  ext
  simp [SetLike.mem_coe, Ideal.mem_span_singleton, hv.dvd_iff_le]

lemma bijective_algebraMap_of_subsingleton_units_mrange (hv : Integers v O)
    [Subsingleton (MonoidHom.mrange v)ˣ] :
    Function.Bijective (algebraMap O F) := by
  refine ⟨hv.hom_inj, fun x ↦ hv.exists_of_le_one ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  · exact (congr_arg Units.val (Subsingleton.elim (α := (MonoidHom.mrange v)ˣ)
      ((isUnit_iff_ne_zero.mpr hx).unit.map v.toMonoidHom.mrangeRestrict) 1)).le

lemma isPrincipal_iff_exists_isGreatest (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ ∃ x, IsGreatest (v ∘ algebraMap O F '' I) x := by
  constructor <;> rintro ⟨x, hx⟩
  · refine ⟨(v ∘ algebraMap O F) x, ?_, ?_⟩
    · refine Set.mem_image_of_mem _ ?_
      simp [hx, Ideal.mem_span_singleton_self]
    · intro y hy
      simp only [Function.comp_apply, hx, Ideal.submodule_span_eq, Set.mem_image,
        SetLike.mem_coe, Ideal.mem_span_singleton] at hy
      obtain ⟨y, hy, rfl⟩ := hy
      exact le_of_dvd hv hy
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [Ideal.submodule_span_eq, Ideal.mem_span_singleton]
    exact ⟨fun hb ↦ dvd_of_le hv (hx.2 <| mem_image_of_mem _ hb), fun hb ↦ I.mem_of_dvd hb ha⟩

lemma isPrincipal_iff_exists_eq_setOf_valuation_le (hv : Integers v O) {I : Ideal O} :
    I.IsPrincipal ↔ ∃ x, (I : Set O) = {y | v (algebraMap O F y) ≤ v (algebraMap O F x)} := by
  rw [isPrincipal_iff_exists_isGreatest hv]
  constructor <;> rintro ⟨x, hx⟩
  · obtain ⟨a, ha, rfl⟩ : ∃ a ∈ I, (v ∘ algebraMap O F) a = x := by simpa using hx.left
    refine ⟨a, ?_⟩
    ext b
    simp only [SetLike.mem_coe, mem_setOf_eq]
    constructor <;> intro h
    · exact hx.right (Set.mem_image_of_mem _ h)
    · rw [le_iff_dvd hv] at h
      exact Ideal.mem_of_dvd I h ha
  · refine ⟨v (algebraMap O F x), Set.mem_image_of_mem _ ?_, ?_⟩
    · simp [hx]
    · simp [hx, mem_upperBounds]

lemma not_denselyOrdered_of_isPrincipalIdealRing [IsPrincipalIdealRing O] (hv : Integers v O) :
    ¬ DenselyOrdered (range v) := by
  intro H
  -- nonunits as an ideal isn't defined here, nor shown to be equivalent to `v x < 1`
  set I : Ideal O := {
    carrier := v ∘ algebraMap O F ⁻¹' Iio (1 : Γ₀)
    add_mem' := fun {a b} ha hb ↦ by simpa using map_add_lt v ha hb
    zero_mem' := by simp
    smul_mem' := by
      intro c x
      simp only [mem_preimage, Function.comp_apply, mem_Iio, smul_eq_mul, map_mul]
      intro hx
      exact Right.mul_lt_one_of_le_of_lt (hv.map_le_one c) hx
  }
  obtain ⟨x, hx₁, hx⟩ :
    ∃ x, v (algebraMap O F x) < 1 ∧
      v (algebraMap O F x) ∈ upperBounds (Iio 1 ∩ range (v ∘ algebraMap O F)) := by
    simpa [I, IsGreatest, hv.isPrincipal_iff_exists_isGreatest, ← image_preimage_eq_inter_range]
      using IsPrincipalIdealRing.principal I
  obtain ⟨y, hy, hy₁⟩ : ∃ y, v (algebraMap O F x) < v y ∧ v y < 1 := by
    simpa only [Subtype.exists, Subtype.mk_lt_mk, exists_range_iff, exists_prop]
      using H.dense ⟨v (algebraMap O F x), mem_range_self _⟩ ⟨1, 1, v.map_one⟩ hx₁
  obtain ⟨z, rfl⟩ := hv.exists_of_le_one hy₁.le
  exact hy.not_ge <| hx ⟨hy₁, mem_range_self _⟩

end Integers

open Integers in

theorem Integer.not_isUnit_iff_valuation_lt_one {x : v.integer} : ¬IsUnit x ↔ v x < 1 := by
  rw [← not_le, not_iff_not, isUnit_iff_valuation_eq_one (F := F) (Γ₀ := Γ₀),
    le_antisymm_iff]
  exacts [and_iff_right x.2, integer.integers v]

namespace integer

lemma v_irreducible_lt_one {ϖ : v.integer} (h : Irreducible ϖ) :
    v ϖ < 1 :=
  (Valuation.integer.integers v).valuation_irreducible_lt_one h

lemma v_irreducible_pos {ϖ : v.integer} (h : Irreducible ϖ) : 0 < v ϖ :=
  (Valuation.integer.integers v).valuation_irreducible_pos h

lemma coe_span_singleton_eq_setOf_le_v_coe (x : v.integer) :
    (Ideal.span {x} : Set v.integer) = {y : v.integer | v y ≤ v x} :=
  (Valuation.integer.integers v).coe_span_singleton_eq_setOf_le_v_algebraMap x

end integer

end Field

section Ideal

variable {R : Type u} {Γ₀ : Type v} [Ring R] [LinearOrderedCommGroupWithZero Γ₀]

variable (v : Valuation R Γ₀)

local notation "𝓞" => v.integer

def leSubmodule (γ : Γ₀) : Submodule 𝓞 R where
  __ := leAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_le_of_le_one_of_le r.prop h

def ltSubmodule (γ : Γ₀ˣ) : Submodule 𝓞 R where
  __ := ltAddSubgroup v γ
  smul_mem' r x h := by
    simpa [Subring.smul_def] using mul_lt_of_le_one_of_lt r.prop h

lemma leSubmodule_monotone : Monotone (leSubmodule v) :=
  leAddSubgroup_monotone v

lemma ltSubmodule_monotone : Monotone (ltSubmodule v) :=
  ltAddSubgroup_monotone v

lemma ltSubmodule_le_leSubmodule (γ : Γ₀ˣ) :
    ltSubmodule v γ ≤ leSubmodule v (γ : Γ₀) :=
  ltAddSubgroup_le_leAddSubgroup v γ

variable {v} in
