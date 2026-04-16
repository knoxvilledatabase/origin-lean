/-
Extracted from Data/Rat/Floor.lean
Genuine: 18 | Conflates: 0 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Order.Floor
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section

/-!
# Floor Function for Rational Numbers

## Summary

We define the `FloorRing` instance on `ℚ`. Some technical lemmas relating `floor` to integer
division and modulo arithmetic are derived as well as some simple inequalities.

## Tags

rat, rationals, ℚ, floor
-/

open Int

namespace Rat

variable {α : Type*} [LinearOrderedField α] [FloorRing α]

protected theorem floor_def' (a : ℚ) : a.floor = a.num / a.den := by
  rw [Rat.floor]
  split
  · next h => simp [h]
  · next => rfl

protected theorem le_floor {z : ℤ} : ∀ {r : ℚ}, z ≤ Rat.floor r ↔ (z : ℚ) ≤ r
  | ⟨n, d, h, c⟩ => by
    simp only [Rat.floor_def']
    rw [mk'_eq_divInt]
    have h' := Int.ofNat_lt.2 (Nat.pos_of_ne_zero h)
    conv =>
      rhs
      rw [intCast_eq_divInt, Rat.divInt_le_divInt zero_lt_one h', mul_one]
    exact Int.le_ediv_iff_mul_le h'

instance : FloorRing ℚ :=
  (FloorRing.ofFloor ℚ Rat.floor) fun _ _ => Rat.le_floor.symm

protected theorem floor_def {q : ℚ} : ⌊q⌋ = q.num / q.den := Rat.floor_def' q

@[norm_cast]
theorem floor_intCast_div_natCast (n : ℤ) (d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / (↑d : ℤ) := by
  rw [Rat.floor_def]
  obtain rfl | hd := @eq_zero_or_pos _ _ d
  · simp
  set q := (n : ℚ) / d with q_eq
  obtain ⟨c, n_eq_c_mul_num, d_eq_c_mul_denom⟩ : ∃ c, n = c * q.num ∧ (d : ℤ) = c * q.den := by
    rw [q_eq]
    exact mod_cast @Rat.exists_eq_mul_div_num_and_eq_mul_div_den n d (mod_cast hd.ne')
  rw [n_eq_c_mul_num, d_eq_c_mul_denom]
  refine (Int.mul_ediv_mul_of_pos _ _ <| pos_of_mul_pos_left ?_ <| Int.natCast_nonneg q.den).symm
  rwa [← d_eq_c_mul_denom, Int.natCast_pos]

@[norm_cast]
theorem floor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋ = n / d :=
  floor_intCast_div_natCast n d

@[norm_cast]
theorem natFloor_natCast_div_natCast (n d : ℕ) : ⌊(↑n / ↑d : ℚ)⌋₊ = n / d := by
  rw [← Int.ofNat_inj, Int.natCast_floor_eq_floor (by positivity)]
  push_cast
  exact floor_intCast_div_natCast n d

@[simp, norm_cast]
theorem floor_cast (x : ℚ) : ⌊(x : α)⌋ = ⌊x⌋ :=
  floor_eq_iff.2 (mod_cast floor_eq_iff.1 (Eq.refl ⌊x⌋))

@[simp, norm_cast]
theorem ceil_cast (x : ℚ) : ⌈(x : α)⌉ = ⌈x⌉ := by
  rw [← neg_inj, ← floor_neg, ← floor_neg, ← Rat.cast_neg, Rat.floor_cast]

@[simp, norm_cast]
theorem round_cast (x : ℚ) : round (x : α) = round x := by
  have : ((x + 1 / 2 : ℚ) : α) = x + 1 / 2 := by simp
  rw [round_eq, round_eq, ← this, floor_cast]

@[simp, norm_cast]
theorem cast_fract (x : ℚ) : (↑(fract x) : α) = fract (x : α) := by
  simp only [fract, cast_sub, cast_intCast, floor_cast]

section NormNum

open Mathlib.Meta.NormNum Qq

theorem isNat_intFloor {R} [LinearOrderedRing R] [FloorRing R] (r : R) (m : ℕ) :
    IsNat r m → IsNat ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intFloor {R} [LinearOrderedRing R] [FloorRing R] (r : R) (m : ℤ) :
    IsInt r m → IsInt ⌊r⌋ m := by rintro ⟨⟨⟩⟩; exact ⟨by simp⟩

theorem isInt_intFloor_ofIsRat (r : α) (n : ℤ) (d : ℕ) :
    IsRat r n d → IsInt ⌊r⌋ (n / d) := by
  rintro ⟨inv, rfl⟩
  constructor
  simp only [invOf_eq_inv, ← div_eq_mul_inv, Int.cast_id]
  rw [← floor_intCast_div_natCast n d, ← floor_cast (α := α), Rat.cast_div,
    cast_intCast, cast_natCast]

@[norm_num ⌊_⌋]
def evalIntFloor : NormNumExt where eval {u αZ} e := do
  match u, αZ, e with
  | 0, ~q(ℤ), ~q(@Int.floor $α $instR $instF $x) =>
    match ← derive x with
    | .isBool .. => failure
    | .isNat _ _ pb => do
      assertInstancesCommute
      return .isNat q(inferInstance) _ q(isNat_intFloor $x _ $pb)
    | .isNegNat _ _ pb => do
      assertInstancesCommute
      -- floor always keeps naturals negative, so we can shortcut `.isInt`
      return .isNegNat q(inferInstance) _ q(isInt_intFloor _ _ $pb)
    | .isRat _ q n d h => do
      let _i ← synthInstanceQ q(LinearOrderedField $α)
      assertInstancesCommute
      have z : Q(ℤ) := mkRawIntLit ⌊q⌋
      letI : $z =Q ⌊$n / $d⌋ := ⟨⟩
      return .isInt q(inferInstance) z ⌊q⌋ q(isInt_intFloor_ofIsRat _ $n $d $h)
  | _, _, _ => failure

end NormNum

end Rat

theorem Int.mod_nat_eq_sub_mul_floor_rat_div {n : ℤ} {d : ℕ} : n % d = n - d * ⌊(n : ℚ) / d⌋ := by
  rw [eq_sub_of_add_eq <| Int.emod_add_ediv n d, Rat.floor_intCast_div_natCast]

theorem Nat.coprime_sub_mul_floor_rat_div_of_coprime {n d : ℕ} (n_coprime_d : n.Coprime d) :
    ((n : ℤ) - d * ⌊(n : ℚ) / d⌋).natAbs.Coprime d := by
  have : (n : ℤ) % d = n - d * ⌊(n : ℚ) / d⌋ := Int.mod_nat_eq_sub_mul_floor_rat_div
  rw [← this]
  have : d.Coprime n := n_coprime_d.symm
  rwa [Nat.Coprime, Nat.gcd_rec] at this

namespace Rat

end Rat
