/-
Extracted from NumberTheory/LegendreSymbol/AddCharacter.lean
Genuine: 16 of 25 | Dissolved: 9 | Infrastructure: 0
-/
import Origin.Core

/-!
# Additive characters of finite rings and fields

This file collects some results on additive characters whose domain is (the additive group of)
a finite ring or field.

## Main definitions and results

We define an additive character `ψ` to be *primitive* if `mulShift ψ a` is trivial only when
`a = 0`.

We show that when `ψ` is primitive, then the map `a ↦ mulShift ψ a` is injective
(`AddChar.to_mulShift_inj_of_isPrimitive`) and that `ψ` is primitive when `R` is a field
and `ψ` is nontrivial (`AddChar.IsNontrivial.isPrimitive`).

We also show that there are primitive additive characters on `R` (with suitable
target `R'`) when `R` is a field or `R = ZMod n` (`AddChar.primitiveCharFiniteField`
and `AddChar.primitiveZModChar`).

Finally, we show that the sum of all character values is zero when the character
is nontrivial (and the target is a domain); see `AddChar.sum_eq_zero_of_isNontrivial`.

## Tags

additive character
-/

universe u v

namespace AddChar

section Additive

variable {R : Type u} [CommRing R] {R' : Type v} [CommMonoid R']

lemma val_mem_rootsOfUnity (φ : AddChar R R') (a : R) (h : 0 < ringChar R) :
    (φ.val_isUnit a).unit ∈ rootsOfUnity (ringChar R).toPNat' R' := by
  simp only [mem_rootsOfUnity', IsUnit.unit_spec, Nat.toPNat'_coe, h, ↓reduceIte,
    ← map_nsmul_eq_pow, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul, map_zero_eq_one]

def IsPrimitive (ψ : AddChar R R') : Prop := ∀ ⦃a : R⦄, a ≠ 0 → mulShift ψ a ≠ 1

lemma IsPrimitive.compMulHom_of_isPrimitive {R'' : Type*} [CommMonoid R''] {φ : AddChar R R'}
    {f : R' →* R''} (hφ : φ.IsPrimitive) (hf : Function.Injective f) :
    (f.compAddChar φ).IsPrimitive := fun a ha ↦ by
  simpa [DFunLike.ext_iff] using (MonoidHom.compAddChar_injective_right f hf).ne (hφ ha)

theorem to_mulShift_inj_of_isPrimitive {ψ : AddChar R R'} (hψ : IsPrimitive ψ) :
    Function.Injective ψ.mulShift := by
  intro a b h
  apply_fun fun x => x * mulShift ψ (-b) at h
  simp only [mulShift_mul, mulShift_zero, add_neg_cancel] at h
  simpa [← sub_eq_add_neg, sub_eq_zero] using (hψ · h)

-- DISSOLVED: IsPrimitive.of_ne_one

lemma not_isPrimitive_mulShift [Finite R] (e : AddChar R R') {r : R}
    (hr : ¬ IsUnit r) : ¬ IsPrimitive (e.mulShift r) := by
  simp only [IsPrimitive, not_forall]
  simp only [isUnit_iff_mem_nonZeroDivisors_of_finite,
    mem_nonZeroDivisors_iff_right, not_forall] at hr
  rcases hr with ⟨x, h, h'⟩
  exact ⟨x, h', by simp only [mulShift_mulShift, mul_comm r, h, mulShift_zero, not_ne_iff]⟩

structure PrimitiveAddChar (R : Type u) [CommRing R] (R' : Type v) [Field R'] where
  /-- The first projection from `PrimitiveAddChar`, giving the cyclotomic field. -/
  n : ℕ+
  /-- The second projection from `PrimitiveAddChar`, giving the character. -/
  char : AddChar R (CyclotomicField n R')
  /-- The third projection from `PrimitiveAddChar`, showing that `χ.char` is primitive. -/
  prim : IsPrimitive char

/-!
### Additive characters on `ZMod n`
-/

section ZMod

variable {N : ℕ} [NeZero N] {R : Type*} [CommRing R] (e : AddChar (ZMod N) R)

lemma exists_divisor_of_not_isPrimitive (he : ¬e.IsPrimitive) :
    ∃ d : ℕ, d ∣ N ∧ d < N ∧ e.mulShift d = 1 := by
  simp_rw [IsPrimitive, not_forall, not_ne_iff] at he
  rcases he with ⟨b, hb_ne, hb⟩
  -- We have `AddChar.mulShift e b = 1`, but `b ≠ 0`.
  obtain ⟨d, hd, u, hu, rfl⟩ := b.eq_unit_mul_divisor
  refine ⟨d, hd, lt_of_le_of_ne (Nat.le_of_dvd (NeZero.pos _) hd) ?_, ?_⟩
  · exact fun h ↦ by simp only [h, ZMod.natCast_self, mul_zero, ne_eq, not_true_eq_false] at hb_ne
  · rw [← mulShift_unit_eq_one_iff _ hu, ← hb, mul_comm]
    ext1 y
    rw [mulShift_apply, mulShift_apply, mulShift_apply, mul_assoc]

end ZMod

section ZModChar

variable {C : Type v} [CommMonoid C]

section ZModCharDef

-- DISSOLVED: zmodChar

-- DISSOLVED: zmodChar_apply

-- DISSOLVED: zmodChar_apply'

end ZModCharDef

-- DISSOLVED: zmod_char_ne_one_iff

-- DISSOLVED: IsPrimitive.zmod_char_eq_one_iff

theorem zmod_char_primitive_of_eq_one_only_at_zero (n : ℕ) (ψ : AddChar (ZMod n) C)
    (hψ : ∀ a, ψ a = 1 → a = 0) : IsPrimitive ψ := by
  refine fun a ha hf => ?_
  have h : mulShift ψ a 1 = (1 : AddChar (ZMod n) C) (1 : ZMod n) :=
    congr_fun (congr_arg (↑) hf) 1
  rw [mulShift_apply, mul_one] at h; norm_cast at h
  exact ha (hψ a h)

-- DISSOLVED: zmodChar_primitive_of_primitive_root

set_option backward.isDefEq.respectTransparency false in

-- DISSOLVED: primitiveZModChar

end ZModChar

end Additive

/-!
### Existence of a primitive additive character on a finite field
-/

noncomputable def FiniteField.primitiveChar (F F' : Type*) [Field F] [Finite F] [Field F']
    (h : ringChar F' ≠ ringChar F) : PrimitiveAddChar F F' := by
  let p := ringChar F
  haveI hp : Fact p.Prime := ⟨CharP.char_is_prime F _⟩
  let pp := p.toPNat hp.1.pos
  have hp₂ : ¬ringChar F' ∣ p := by
    rcases CharP.char_is_prime_or_zero F' (ringChar F') with hq | hq
    · exact mt (Nat.Prime.dvd_iff_eq hp.1 (Nat.Prime.ne_one hq)).mp h.symm
    · rw [hq]
      exact fun hf => Nat.Prime.ne_zero hp.1 (zero_dvd_iff.mp hf)
  let ψ := primitiveZModChar pp F' (neZero_iff.mp (NeZero.of_not_dvd F' hp₂))
  letI : Algebra (ZMod p) F := ZMod.algebra _ _
  let ψ' := ψ.char.compAddMonoidHom (Algebra.trace (ZMod p) F).toAddMonoidHom
  have hψ' : ψ' ≠ 1 := by
    obtain ⟨a, ha⟩ := FiniteField.trace_to_zmod_nondegenerate F one_ne_zero
    rw [one_mul] at ha
    exact ne_one_iff.2
      ⟨a, fun hf => ha <| (ψ.prim.zmod_char_eq_one_iff pp <| Algebra.trace (ZMod p) F a).mp hf⟩
  exact ⟨ψ.n, ψ', IsPrimitive.of_ne_one hψ'⟩

/-!
### The sum of all character values
-/

section sum

variable {R : Type*} [AddGroup R] [Fintype R] {R' : Type*} [CommRing R']

-- DISSOLVED: sum_eq_zero_of_ne_one

theorem sum_eq_card_of_eq_one {ψ : AddChar R R'} (hψ : ψ = 1) :
    ∑ a, ψ a = Fintype.card R := by simp [hψ]

end sum

theorem sum_mulShift {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
    {R' : Type*} [CommRing R'] [IsDomain R'] {ψ : AddChar R R'} (b : R)
    (hψ : IsPrimitive ψ) : ∑ x : R, ψ (x * b) = if b = 0 then Fintype.card R else 0 := by
  split_ifs with h
  · -- case `b = 0`
    simp only [h, mul_zero, map_zero_eq_one, Finset.sum_const, Nat.smul_one_eq_cast]
    rfl
  · -- case `b ≠ 0`
    simp_rw [mul_comm]
    exact mod_cast sum_eq_zero_of_ne_one (hψ h)

/-!
### Complex-valued additive characters
-/

section Ring

variable {R : Type*} [CommRing R]

lemma starComp_eq_inv (hR : 0 < ringChar R) {φ : AddChar R ℂ} :
    (starRingEnd ℂ).compAddChar φ = φ⁻¹ := by
  ext1 a
  simp only [RingHom.toMonoidHom_eq_coe, MonoidHom.coe_compAddChar, MonoidHom.coe_coe,
    Function.comp_apply, inv_apply']
  have H := Complex.norm_eq_one_of_mem_rootsOfUnity <| φ.val_mem_rootsOfUnity a hR
  exact (Complex.inv_eq_conj H).symm

lemma starComp_apply (hR : 0 < ringChar R) {φ : AddChar R ℂ} (a : R) :
    (starRingEnd ℂ) (φ a) = φ⁻¹ a := by
  rw [← starComp_eq_inv hR]
  rfl

end Ring

section Field

variable (F : Type*) [Field F] [Finite F]

private lemma ringChar_ne : ringChar ℂ ≠ ringChar F := by
  simpa only [ringChar.eq_zero] using (CharP.ringChar_ne_zero_of_finite F).symm

set_option backward.isDefEq.respectTransparency false in

noncomputable def FiniteField.primitiveChar_to_Complex : AddChar F ℂ := by
  letI ch := primitiveChar F ℂ <| by exact ringChar_ne F
  refine MonoidHom.compAddChar ?_ ch.char
  exact (IsCyclotomicExtension.algEquiv {(ch.n : ℕ)} ℂ (CyclotomicField ch.n ℂ) ℂ).toMonoidHom

set_option backward.isDefEq.respectTransparency false in

lemma FiniteField.primitiveChar_to_Complex_isPrimitive :
    (primitiveChar_to_Complex F).IsPrimitive := by
  refine IsPrimitive.compMulHom_of_isPrimitive (PrimitiveAddChar.prim _) ?_
  let nn := (primitiveChar F ℂ <| ringChar_ne F).n
  exact (IsCyclotomicExtension.algEquiv {(nn : ℕ)} ℂ (CyclotomicField nn ℂ) ℂ).injective

end Field

end AddChar
