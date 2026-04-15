/-
Extracted from NumberTheory/Ostrowski.lean
Genuine: 7 of 7 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ostrowski’s Theorem

Ostrowski's Theorem for the field `ℚ`: every absolute value on `ℚ` is equivalent to either a
`p`-adic absolute value or to the standard Archimedean (Euclidean) absolute value.

## Main results

- `Rat.AbsoluteValue.equiv_real_or_padic`: given an absolute value on `ℚ`, it is equivalent
  to the standard Archimedean (Euclidean) absolute value `Rat.AbsoluteValue.real` or to a `p`-adic
  absolute value `Rat.AbsoluteValue.padic p` for a unique prime number `p`.

## TODO

Extend to arbitrary number fields.

## References

* [K. Conrad, *Ostrowski's Theorem for Q*][conradQ]
* [K. Conrad, *Ostrowski for number fields*][conradnumbfield]
* [J. W. S. Cassels, *Local fields*][cassels1986local]

## Tags

absolute value, Ostrowski's theorem
-/

open Filter Nat Real Topology

private lemma tendsto_const_rpow_inv {C : ℝ} (hC : 0 < C) :
    Tendsto (fun k : ℕ ↦ C ^ (k : ℝ)⁻¹) atTop (𝓝 1) :=
  ((continuous_iff_continuousAt.mpr fun _ ↦ continuousAt_const_rpow hC.ne').tendsto'
    0 1 (rpow_zero C)).comp <| tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop

private lemma tendsto_nat_rpow_inv :
    Tendsto (fun k : ℕ ↦ (k : ℝ) ^ (k : ℝ)⁻¹) atTop (𝓝 1) := by
  simp_rw [← one_div]
  exact Tendsto.comp tendsto_rpow_div tendsto_natCast_atTop_atTop

private lemma list_mul_sum {R : Type*} [Semiring R] {T : Type*} (l : List T) (y : R) (x : R) :
    (l.mapIdx fun i _ => x * y ^ i).sum = x * (l.mapIdx fun i _ => y ^ i).sum := by
  simp_rw [← smul_eq_mul, List.smul_sum, List.mapIdx_eq_zipIdx_map]
  congr 1
  simp

private lemma list_geom {T : Type*} {F : Type*} [DivisionRing F] (l : List T) {y : F} (hy : y ≠ 1) :
    (l.mapIdx fun i _ => y ^ i).sum = (y ^ l.length - 1) / (y - 1) := by
  rw [← geom_sum_eq hy l.length, List.mapIdx_eq_zipIdx_map, Finset.sum_range,
    ← Fin.sum_univ_fun_getElem]
  simp only
  let e : Fin l.zipIdx.length ≃ Fin l.length := finCongr List.length_zipIdx
  exact Fintype.sum_bijective e e.bijective _ _ fun _ ↦ by simp [e]

open AbsoluteValue -- does not work as intended after `namespace Rat.AbsoluteValue`

namespace Rat.AbsoluteValue

/-!
### Preliminary lemmas
-/

open Int

variable {f g : AbsoluteValue ℚ ℝ}

lemma eq_on_nat_iff_eq : (∀ n : ℕ, f n = g n) ↔ f = g := by
  refine ⟨fun h ↦ ?_, fun h n ↦ congrFun (congrArg DFunLike.coe h) ↑n⟩
  ext1 z
  rw [← Rat.num_div_den z, map_div₀, map_div₀, h, eq_on_nat_iff_eq_on_int.mp h]

lemma exists_nat_rpow_iff_isEquiv : (∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, f n ^ c = g n) ↔ f.IsEquiv g := by
  rw [isEquiv_iff_exists_rpow_eq]
  refine ⟨fun ⟨c, hc, h⟩ ↦ ⟨c, hc, ?_⟩, fun ⟨c, hc, h⟩ ↦ ⟨c, hc, (congrFun h ·)⟩⟩
  ext1 x
  rw [← Rat.num_div_den x, map_div₀, map_div₀, div_rpow (by positivity) (by positivity), h x.den,
    ← apply_natAbs_eq, ← apply_natAbs_eq, h (natAbs x.num)]

section Non_archimedean

/-!
### The non-archimedean case

Every bounded absolute value on `ℚ` is equivalent to a `p`-adic absolute value.
-/

def padic (p : ℕ) [Fact p.Prime] : AbsoluteValue ℚ ℝ where
  toFun x := (padicNorm p x : ℝ)
  map_mul' := by simp only [padicNorm.mul, Rat.cast_mul, forall_const]
  nonneg' x := cast_nonneg.mpr <| padicNorm.nonneg x
  eq_zero' x :=
    ⟨fun H ↦ padicNorm.zero_of_padicNorm_eq_zero <| cast_eq_zero.mp H,
      fun H ↦ cast_eq_zero.mpr <| H ▸ padicNorm.zero (p := p)⟩
  add_le' x y := by exact_mod_cast padicNorm.triangle_ineq x y
