/-
Extracted from Analysis/SpecialFunctions/Pow/NNReal.lean
Genuine: 144 | Conflates: 0 | Dissolved: 47 | Infrastructure: 9
-/
import Origin.Core
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Power function on `ℝ≥0` and `ℝ≥0∞`

We construct the power functions `x ^ y` where
* `x` is a nonnegative real number and `y` is a real number;
* `x` is a number from `[0, +∞]` (a.k.a. `ℝ≥0∞`) and `y` is a real number.

We also prove basic properties of these functions.
-/

noncomputable section

open scoped Classical

open Real NNReal ENNReal ComplexConjugate

open Finset Function Set

namespace NNReal

variable {x : ℝ≥0} {w y z : ℝ}

noncomputable def rpow (x : ℝ≥0) (y : ℝ) : ℝ≥0 :=
  ⟨(x : ℝ) ^ y, Real.rpow_nonneg x.2 y⟩

noncomputable instance : Pow ℝ≥0 ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp, norm_cast]
theorem coe_rpow (x : ℝ≥0) (y : ℝ) : ((x ^ y : ℝ≥0) : ℝ) = (x : ℝ) ^ y :=
  rfl

@[simp]
theorem rpow_zero (x : ℝ≥0) : x ^ (0 : ℝ) = 1 :=
  NNReal.eq <| Real.rpow_zero _

-- DISSOLVED: rpow_eq_zero_iff

-- DISSOLVED: rpow_eq_zero

-- DISSOLVED: zero_rpow

@[simp]
theorem rpow_one (x : ℝ≥0) : x ^ (1 : ℝ) = x :=
  NNReal.eq <| Real.rpow_one _

lemma rpow_neg (x : ℝ≥0) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.rpow_neg x.2 _

@[simp, norm_cast]
lemma rpow_natCast (x : ℝ≥0) (n : ℕ) : x ^ (n : ℝ) = x ^ n :=
  NNReal.eq <| by simpa only [coe_rpow, coe_pow] using Real.rpow_natCast x n

@[simp, norm_cast]
lemma rpow_intCast (x : ℝ≥0) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_coe, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0) ^ x = 1 :=
  NNReal.eq <| Real.one_rpow _

-- DISSOLVED: rpow_add

-- DISSOLVED: rpow_add'

-- DISSOLVED: rpow_add_intCast

-- DISSOLVED: rpow_add_natCast

-- DISSOLVED: rpow_sub_intCast

-- DISSOLVED: rpow_sub_natCast

-- DISSOLVED: rpow_add_intCast'

-- DISSOLVED: rpow_add_natCast'

-- DISSOLVED: rpow_sub_intCast'

-- DISSOLVED: rpow_sub_natCast'

-- DISSOLVED: rpow_add_one

-- DISSOLVED: rpow_sub_one

-- DISSOLVED: rpow_add_one'

-- DISSOLVED: rpow_one_add'

theorem rpow_add_of_nonneg (x : ℝ≥0) {y z : ℝ} (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  ext; exact Real.rpow_add_of_nonneg x.2 hy hz

-- DISSOLVED: rpow_of_add_eq

theorem rpow_mul (x : ℝ≥0) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z :=
  NNReal.eq <| Real.rpow_mul x.2 y z

lemma rpow_natCast_mul (x : ℝ≥0) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_mul_natCast (x : ℝ≥0) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_intCast_mul (x : ℝ≥0) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_mul_intCast (x : ℝ≥0) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]

theorem rpow_neg_one (x : ℝ≥0) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]

-- DISSOLVED: rpow_sub

-- DISSOLVED: rpow_sub'

-- DISSOLVED: rpow_sub_one'

-- DISSOLVED: rpow_one_sub'

-- DISSOLVED: rpow_inv_rpow_self

-- DISSOLVED: rpow_self_rpow_inv

theorem inv_rpow (x : ℝ≥0) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ :=
  NNReal.eq <| Real.inv_rpow x.2 y

theorem div_rpow (x y : ℝ≥0) (z : ℝ) : (x / y) ^ z = x ^ z / y ^ z :=
  NNReal.eq <| Real.div_rpow x.2 y.2 z

theorem sqrt_eq_rpow (x : ℝ≥0) : sqrt x = x ^ (1 / (2 : ℝ)) := by
  refine NNReal.eq ?_
  push_cast
  exact Real.sqrt_eq_rpow x.1

alias rpow_nat_cast := rpow_natCast

@[simp]
lemma rpow_ofNat (x : ℝ≥0) (n : ℕ) [n.AtLeastTwo] :
    x ^ (no_index (OfNat.ofNat n) : ℝ) = x ^ (OfNat.ofNat n : ℕ) :=
  rpow_natCast x n

theorem rpow_two (x : ℝ≥0) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2

theorem mul_rpow {x y : ℝ≥0} {z : ℝ} : (x * y) ^ z = x ^ z * y ^ z :=
  NNReal.eq <| Real.mul_rpow x.2 y.2

@[simps]
def rpowMonoidHom (r : ℝ) : ℝ≥0 →* ℝ≥0 where
  toFun := (· ^ r)
  map_one' := one_rpow _
  map_mul' _x _y := mul_rpow

theorem list_prod_map_rpow (l : List ℝ≥0) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r :=
  l.prod_hom (rpowMonoidHom r)

theorem list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ≥0) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← list_prod_map_rpow, List.map_map]; rfl

lemma multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r :=
  s.prod_hom' (rpowMonoidHom r) _

lemma finset_prod_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
  multiset_prod_map_rpow _ _ _

section Real

theorem _root_.Real.list_prod_map_rpow (l : List ℝ) (hl : ∀ x ∈ l, (0 : ℝ) ≤ x) (r : ℝ) :
    (l.map (· ^ r)).prod = l.prod ^ r := by
  lift l to List ℝ≥0 using hl
  have := congr_arg ((↑) : ℝ≥0 → ℝ) (NNReal.list_prod_map_rpow l r)
  push_cast at this
  rw [List.map_map] at this ⊢
  exact mod_cast this

theorem _root_.Real.list_prod_map_rpow' {ι} (l : List ι) (f : ι → ℝ)
    (hl : ∀ i ∈ l, (0 : ℝ) ≤ f i) (r : ℝ) :
    (l.map (f · ^ r)).prod = (l.map f).prod ^ r := by
  rw [← Real.list_prod_map_rpow (l.map f) _ r, List.map_map]
  · rfl
  simpa using hl

theorem _root_.Real.multiset_prod_map_rpow {ι} (s : Multiset ι) (f : ι → ℝ)
    (hs : ∀ i ∈ s, (0 : ℝ) ≤ f i) (r : ℝ) :
    (s.map (f · ^ r)).prod = (s.map f).prod ^ r := by
  induction' s using Quotient.inductionOn with l
  simpa using Real.list_prod_map_rpow' l f hs r

theorem _root_.Real.finset_prod_rpow
    {ι} (s : Finset ι) (f : ι → ℝ) (hs : ∀ i ∈ s, 0 ≤ f i) (r : ℝ) :
    (∏ i ∈ s, f i ^ r) = (∏ i ∈ s, f i) ^ r :=
  Real.multiset_prod_map_rpow s.val f hs r

end Real

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  Real.rpow_le_rpow x.2 h₁ h₂

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  Real.rpow_lt_rpow x.2 h₁ h₂

theorem rpow_lt_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  Real.rpow_lt_rpow_iff x.2 y.2 hz

theorem rpow_le_rpow_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  Real.rpow_le_rpow_iff x.2 y.2 hz

theorem le_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']

theorem le_rpow_one_div_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']

theorem rpow_inv_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, ← one_div, rpow_self_rpow_inv hz.ne']

theorem rpow_one_div_le_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  rw [← rpow_le_rpow_iff hz, rpow_self_rpow_inv hz.ne']

theorem lt_rpow_inv_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^z < y := by
  simp only [← not_le, rpow_inv_le_iff hz]

theorem rpow_inv_lt_iff {x y : ℝ≥0} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

section

variable {y : ℝ≥0}

lemma rpow_lt_rpow_of_neg (hx : 0 < x) (hxy : x < y) (hz : z < 0) : y ^ z < x ^ z :=
  Real.rpow_lt_rpow_of_neg hx hxy hz

lemma rpow_le_rpow_of_nonpos (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) : y ^ z ≤ x ^ z :=
  Real.rpow_le_rpow_of_nonpos hx hxy hz

lemma rpow_lt_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z < y ^ z ↔ y < x :=
  Real.rpow_lt_rpow_iff_of_neg hx hy hz

lemma rpow_le_rpow_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z ≤ y ^ z ↔ y ≤ x :=
  Real.rpow_le_rpow_iff_of_neg hx hy hz

lemma le_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y :=
  Real.le_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_le_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z :=
  Real.rpow_inv_le_iff_of_pos x.2 hy hz

lemma lt_rpow_inv_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x < y ^ z⁻¹ ↔ x ^ z < y :=
  Real.lt_rpow_inv_iff_of_pos x.2 hy hz

lemma rpow_inv_lt_iff_of_pos (hy : 0 ≤ y) (hz : 0 < z) (x : ℝ≥0) : x ^ z⁻¹ < y ↔ x < y ^ z :=
  Real.rpow_inv_lt_iff_of_pos x.2 hy hz

lemma le_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ≤ y ^ z⁻¹ ↔ y ≤ x ^ z :=
  Real.le_rpow_inv_iff_of_neg hx hy hz

lemma lt_rpow_inv_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x < y ^ z⁻¹ ↔ y < x ^ z :=
  Real.lt_rpow_inv_iff_of_neg hx hy hz

lemma rpow_inv_lt_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ < y ↔ y ^ z < x :=
  Real.rpow_inv_lt_iff_of_neg hx hy hz

lemma rpow_inv_le_iff_of_neg (hx : 0 < x) (hy : 0 < y) (hz : z < 0) : x ^ z⁻¹ ≤ y ↔ y ^ z ≤ x :=
  Real.rpow_inv_le_iff_of_neg hx hy hz

end

@[gcongr] theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0} {y z : ℝ} (hx : 1 < x) (hyz : y < z) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_lt hx hyz

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_le hx hyz

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z :=
  Real.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0} {y z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z :=
  Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hyz

theorem rpow_pos {p : ℝ} {x : ℝ≥0} (hx_pos : 0 < x) : 0 < x ^ p := by
  have rpow_pos_of_nonneg : ∀ {p : ℝ}, 0 < p → 0 < x ^ p := by
    intro p hp_pos
    rw [← zero_rpow hp_pos.ne']
    exact rpow_lt_rpow hx_pos hp_pos
  rcases lt_trichotomy (0 : ℝ) p with (hp_pos | rfl | hp_neg)
  · exact rpow_pos_of_nonneg hp_pos
  · simp only [zero_lt_one, rpow_zero]
  · rw [← neg_neg p, rpow_neg, inv_pos]
    exact rpow_pos_of_nonneg (neg_pos.mpr hp_neg)

theorem rpow_lt_one {x : ℝ≥0} {z : ℝ} (hx1 : x < 1) (hz : 0 < z) : x ^ z < 1 :=
  Real.rpow_lt_one (coe_nonneg x) hx1 hz

theorem rpow_le_one {x : ℝ≥0} {z : ℝ} (hx2 : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 :=
  Real.rpow_le_one x.2 hx2 hz

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg hx hz

theorem rpow_le_one_of_one_le_of_nonpos {x : ℝ≥0} {z : ℝ} (hx : 1 ≤ x) (hz : z ≤ 0) : x ^ z ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos hx hz

theorem one_lt_rpow {x : ℝ≥0} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z :=
  Real.one_lt_rpow hx hz

theorem one_le_rpow {x : ℝ≥0} {z : ℝ} (h : 1 ≤ x) (h₁ : 0 ≤ z) : 1 ≤ x ^ z :=
  Real.one_le_rpow h h₁

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z :=
  Real.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz

theorem one_le_rpow_of_pos_of_le_one_of_nonpos {x : ℝ≥0} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z ≤ 0) : 1 ≤ x ^ z :=
  Real.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 hz

theorem rpow_le_self_of_le_one {x : ℝ≥0} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  rcases eq_bot_or_bot_lt x with (rfl | (h : 0 < x))
  · have : z ≠ 0 := by linarith
    simp [this]
  nth_rw 2 [← NNReal.rpow_one x]
  exact NNReal.rpow_le_rpow_of_exponent_ge h hx h_one_le

-- DISSOLVED: rpow_left_injective

-- DISSOLVED: rpow_eq_rpow_iff

-- DISSOLVED: rpow_left_surjective

-- DISSOLVED: rpow_left_bijective

-- DISSOLVED: eq_rpow_inv_iff

-- DISSOLVED: eq_rpow_one_div_iff

-- DISSOLVED: rpow_inv_eq_iff

-- DISSOLVED: rpow_one_div_eq_iff

-- DISSOLVED: rpow_rpow_inv

-- DISSOLVED: rpow_inv_rpow

-- DISSOLVED: pow_rpow_inv_natCast

-- DISSOLVED: rpow_inv_natCast_pow

theorem _root_.Real.toNNReal_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) :
    Real.toNNReal (x ^ y) = Real.toNNReal x ^ y := by
  nth_rw 1 [← Real.coe_toNNReal x hx]
  rw [← NNReal.coe_rpow, Real.toNNReal_coe]

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0 => x ^ z :=
  fun x y hxy => by simp only [NNReal.rpow_lt_rpow hxy h, coe_lt_coe]

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0 => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

@[simps! apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0 ≃o ℝ≥0 :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
      dsimp
      rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]

theorem orderIsoRpow_symm_eq (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]; rfl

theorem _root_.Real.nnnorm_rpow_of_nonneg {x y : ℝ} (hx : 0 ≤ x) : ‖x ^ y‖₊ = ‖x‖₊ ^ y := by
  ext; exact Real.norm_rpow_of_nonneg hx

end NNReal

namespace ENNReal

noncomputable def rpow : ℝ≥0∞ → ℝ → ℝ≥0∞
  | some x, y => if x = 0 ∧ y < 0 then ⊤ else (x ^ y : ℝ≥0)
  | none, y => if 0 < y then ⊤ else if y = 0 then 1 else 0

noncomputable instance : Pow ℝ≥0∞ ℝ :=
  ⟨rpow⟩

@[simp]
theorem rpow_eq_pow (x : ℝ≥0∞) (y : ℝ) : rpow x y = x ^ y :=
  rfl

@[simp]
theorem rpow_zero {x : ℝ≥0∞} : x ^ (0 : ℝ) = 1 := by
  cases x <;>
    · dsimp only [(· ^ ·), Pow.pow, rpow]
      simp [lt_irrefl]

theorem top_rpow_def (y : ℝ) : (⊤ : ℝ≥0∞) ^ y = if 0 < y then ⊤ else if y = 0 then 1 else 0 :=
  rfl

@[simp]
theorem top_rpow_of_pos {y : ℝ} (h : 0 < y) : (⊤ : ℝ≥0∞) ^ y = ⊤ := by simp [top_rpow_def, h]

@[simp]
theorem top_rpow_of_neg {y : ℝ} (h : y < 0) : (⊤ : ℝ≥0∞) ^ y = 0 := by
  simp [top_rpow_def, asymm h, ne_of_lt h]

@[simp]
theorem zero_rpow_of_pos {y : ℝ} (h : 0 < y) : (0 : ℝ≥0∞) ^ y = 0 := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h, asymm h, ne_of_gt h]

@[simp]
theorem zero_rpow_of_neg {y : ℝ} (h : y < 0) : (0 : ℝ≥0∞) ^ y = ⊤ := by
  rw [← ENNReal.coe_zero, ← ENNReal.some_eq_coe]
  dsimp only [(· ^ ·), rpow, Pow.pow]
  simp [h, ne_of_gt h]

theorem zero_rpow_def (y : ℝ) : (0 : ℝ≥0∞) ^ y = if 0 < y then 0 else if y = 0 then 1 else ⊤ := by
  rcases lt_trichotomy (0 : ℝ) y with (H | rfl | H)
  · simp [H, ne_of_gt, zero_rpow_of_pos, lt_irrefl]
  · simp [lt_irrefl]
  · simp [H, asymm H, ne_of_lt, zero_rpow_of_neg]

@[simp]
theorem zero_rpow_mul_self (y : ℝ) : (0 : ℝ≥0∞) ^ y * (0 : ℝ≥0∞) ^ y = (0 : ℝ≥0∞) ^ y := by
  rw [zero_rpow_def]
  split_ifs
  exacts [zero_mul _, one_mul _, top_mul_top]

-- DISSOLVED: coe_rpow_of_ne_zero

@[norm_cast]
theorem coe_rpow_of_nonneg (x : ℝ≥0) {y : ℝ} (h : 0 ≤ y) : ↑(x ^ y) = (x : ℝ≥0∞) ^ y := by
  by_cases hx : x = 0
  · rcases le_iff_eq_or_lt.1 h with (H | H)
    · simp [hx, H.symm]
    · simp [hx, zero_rpow_of_pos H, NNReal.zero_rpow (ne_of_gt H)]
  · exact coe_rpow_of_ne_zero hx _

theorem coe_rpow_def (x : ℝ≥0) (y : ℝ) :
    (x : ℝ≥0∞) ^ y = if x = 0 ∧ y < 0 then ⊤ else ↑(x ^ y) :=
  rfl

@[simp]
theorem rpow_one (x : ℝ≥0∞) : x ^ (1 : ℝ) = x := by
  cases x
  · exact dif_pos zero_lt_one
  · change ite _ _ _ = _
    simp only [NNReal.rpow_one, some_eq_coe, ite_eq_right_iff, top_ne_coe, and_imp]
    exact fun _ => zero_le_one.not_lt

@[simp]
theorem one_rpow (x : ℝ) : (1 : ℝ≥0∞) ^ x = 1 := by
  rw [← coe_one, ← coe_rpow_of_ne_zero one_ne_zero]
  simp

@[simp]
theorem rpow_eq_zero_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = 0 ↔ x = 0 ∧ 0 < y ∨ x = ⊤ ∧ y < 0 := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

lemma rpow_eq_zero_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = 0 ↔ x = 0 := by
  simp [hy, hy.not_lt]

@[simp]
theorem rpow_eq_top_iff {x : ℝ≥0∞} {y : ℝ} : x ^ y = ⊤ ↔ x = 0 ∧ y < 0 ∨ x = ⊤ ∧ 0 < y := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [H, top_rpow_of_neg, top_rpow_of_pos, le_of_lt]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, H, zero_rpow_of_neg, zero_rpow_of_pos, le_of_lt]
    · simp [← coe_rpow_of_ne_zero h, h]

theorem rpow_eq_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y = ⊤ ↔ x = ⊤ := by
  simp [rpow_eq_top_iff, hy, asymm hy]

lemma rpow_lt_top_iff_of_pos {x : ℝ≥0∞} {y : ℝ} (hy : 0 < y) : x ^ y < ∞ ↔ x < ∞ := by
  simp only [lt_top_iff_ne_top, Ne, rpow_eq_top_iff_of_pos hy]

theorem rpow_eq_top_of_nonneg (x : ℝ≥0∞) {y : ℝ} (hy0 : 0 ≤ y) : x ^ y = ⊤ → x = ⊤ := by
  rw [ENNReal.rpow_eq_top_iff]
  rintro (h|h)
  · exfalso
    rw [lt_iff_not_ge] at h
    exact h.right hy0
  · exact h.left

theorem rpow_ne_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y ≠ ⊤ :=
  mt (ENNReal.rpow_eq_top_of_nonneg x hy0) h

theorem rpow_lt_top_of_nonneg {x : ℝ≥0∞} {y : ℝ} (hy0 : 0 ≤ y) (h : x ≠ ⊤) : x ^ y < ⊤ :=
  lt_top_iff_ne_top.mpr (ENNReal.rpow_ne_top_of_nonneg hy0 h)

-- DISSOLVED: rpow_add

theorem rpow_add_of_nonneg {x : ℝ≥0∞} (y z : ℝ) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    x ^ (y + z) = x ^ y * x ^ z := by
  induction x using recTopCoe
  · rcases hy.eq_or_lt with rfl|hy
    · rw [rpow_zero, one_mul, zero_add]
    rcases hz.eq_or_lt with rfl|hz
    · rw [rpow_zero, mul_one, add_zero]
    simp [top_rpow_of_pos, hy, hz, add_pos hy hz]
  simp [← coe_rpow_of_nonneg, hy, hz, add_nonneg hy hz, NNReal.rpow_add_of_nonneg _ hy hz]

theorem rpow_neg (x : ℝ≥0∞) (y : ℝ) : x ^ (-y) = (x ^ y)⁻¹ := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (H | H | H) <;>
      simp [top_rpow_of_pos, top_rpow_of_neg, H, neg_pos.mpr]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (H | H | H) <;>
        simp [h, zero_rpow_of_pos, zero_rpow_of_neg, H, neg_pos.mpr]
    · have A : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero h, ← coe_inv A, NNReal.rpow_neg]

-- DISSOLVED: rpow_sub

theorem rpow_neg_one (x : ℝ≥0∞) : x ^ (-1 : ℝ) = x⁻¹ := by simp [rpow_neg]

theorem rpow_mul (x : ℝ≥0∞) (y z : ℝ) : x ^ (y * z) = (x ^ y) ^ z := by
  cases' x with x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
        rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
      simp [Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
        mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
  · by_cases h : x = 0
    · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
          rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
        simp [h, Hy, Hz, zero_rpow_of_neg, zero_rpow_of_pos, top_rpow_of_neg, top_rpow_of_pos,
          mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, mul_neg_of_pos_of_neg]
    · have : x ^ y ≠ 0 := by simp [h]
      simp [← coe_rpow_of_ne_zero, h, this, NNReal.rpow_mul]

@[simp, norm_cast]
theorem rpow_natCast (x : ℝ≥0∞) (n : ℕ) : x ^ (n : ℝ) = x ^ n := by
  cases x
  · cases n <;> simp [top_rpow_of_pos (Nat.cast_add_one_pos _), top_pow (Nat.succ_pos _)]
  · simp [← coe_rpow_of_nonneg _ (Nat.cast_nonneg n)]

alias rpow_nat_cast := rpow_natCast

@[simp]
lemma rpow_ofNat (x : ℝ≥0∞) (n : ℕ) [n.AtLeastTwo] :
    x ^ (no_index (OfNat.ofNat n) : ℝ) = x ^ (OfNat.ofNat n) :=
  rpow_natCast x n

@[simp, norm_cast]
lemma rpow_intCast (x : ℝ≥0∞) (n : ℤ) : x ^ (n : ℝ) = x ^ n := by
  cases n <;> simp only [Int.ofNat_eq_coe, Int.cast_natCast, rpow_natCast, zpow_natCast,
    Int.cast_negSucc, rpow_neg, zpow_negSucc]

alias rpow_int_cast := rpow_intCast

theorem rpow_two (x : ℝ≥0∞) : x ^ (2 : ℝ) = x ^ 2 := rpow_ofNat x 2

theorem mul_rpow_eq_ite (x y : ℝ≥0∞) (z : ℝ) :
    (x * y) ^ z = if (x = 0 ∧ y = ⊤ ∨ x = ⊤ ∧ y = 0) ∧ z < 0 then ⊤ else x ^ z * y ^ z := by
  rcases eq_or_ne z 0 with (rfl | hz); · simp
  replace hz := hz.lt_or_lt
  wlog hxy : x ≤ y
  · convert this y x z hz (le_of_not_le hxy) using 2 <;> simp only [mul_comm, and_comm, or_comm]
  rcases eq_or_ne x 0 with (rfl | hx0)
  · induction y <;> cases' hz with hz hz <;> simp [*, hz.not_lt]
  rcases eq_or_ne y 0 with (rfl | hy0)
  · exact (hx0 (bot_unique hxy)).elim
  induction x
  · cases' hz with hz hz <;> simp [hz, top_unique hxy]
  induction y
  · rw [ne_eq, coe_eq_zero] at hx0
    cases' hz with hz hz <;> simp [*]
  simp only [*, if_false]
  norm_cast at *
  rw [← coe_rpow_of_ne_zero (mul_ne_zero hx0 hy0), NNReal.mul_rpow]
  norm_cast

theorem mul_rpow_of_ne_top {x y : ℝ≥0∞} (hx : x ≠ ⊤) (hy : y ≠ ⊤) (z : ℝ) :
    (x * y) ^ z = x ^ z * y ^ z := by simp [*, mul_rpow_eq_ite]

@[norm_cast]
theorem coe_mul_rpow (x y : ℝ≥0) (z : ℝ) : ((x : ℝ≥0∞) * y) ^ z = (x : ℝ≥0∞) ^ z * (y : ℝ≥0∞) ^ z :=
  mul_rpow_of_ne_top coe_ne_top coe_ne_top z

theorem prod_coe_rpow {ι} (s : Finset ι) (f : ι → ℝ≥0) (r : ℝ) :
    ∏ i ∈ s, (f i : ℝ≥0∞) ^ r = ((∏ i ∈ s, f i : ℝ≥0) : ℝ≥0∞) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | insert hi ih => simp_rw [prod_insert hi, ih, ← coe_mul_rpow, coe_mul]

-- DISSOLVED: mul_rpow_of_ne_zero

theorem mul_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x * y) ^ z = x ^ z * y ^ z := by
  simp [hz.not_lt, mul_rpow_eq_ite]

theorem prod_rpow_of_ne_top {ι} {s : Finset ι} {f : ι → ℝ≥0∞} (hf : ∀ i ∈ s, f i ≠ ∞) (r : ℝ) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | @insert i s hi ih =>
    have h2f : ∀ i ∈ s, f i ≠ ∞ := fun i hi ↦ hf i <| mem_insert_of_mem hi
    rw [prod_insert hi, prod_insert hi, ih h2f, ← mul_rpow_of_ne_top <| hf i <| mem_insert_self ..]
    apply prod_ne_top h2f

theorem prod_rpow_of_nonneg {ι} {s : Finset ι} {f : ι → ℝ≥0∞} {r : ℝ} (hr : 0 ≤ r) :
    ∏ i ∈ s, f i ^ r = (∏ i ∈ s, f i) ^ r := by
  induction s using Finset.induction with
  | empty => simp
  | insert hi ih => simp_rw [prod_insert hi, ih, ← mul_rpow_of_nonneg _ _ hr]

theorem inv_rpow (x : ℝ≥0∞) (y : ℝ) : x⁻¹ ^ y = (x ^ y)⁻¹ := by
  rcases eq_or_ne y 0 with (rfl | hy); · simp only [rpow_zero, inv_one]
  replace hy := hy.lt_or_lt
  rcases eq_or_ne x 0 with (rfl | h0); · cases hy <;> simp [*]
  rcases eq_or_ne x ⊤ with (rfl | h_top); · cases hy <;> simp [*]
  apply ENNReal.eq_inv_of_mul_eq_one_left
  rw [← mul_rpow_of_ne_zero (ENNReal.inv_ne_zero.2 h_top) h0, ENNReal.inv_mul_cancel h0 h_top,
    one_rpow]

theorem div_rpow_of_nonneg (x y : ℝ≥0∞) {z : ℝ} (hz : 0 ≤ z) : (x / y) ^ z = x ^ z / y ^ z := by
  rw [div_eq_mul_inv, mul_rpow_of_nonneg _ _ hz, inv_rpow, div_eq_mul_inv]

theorem strictMono_rpow_of_pos {z : ℝ} (h : 0 < z) : StrictMono fun x : ℝ≥0∞ => x ^ z := by
  intro x y hxy
  lift x to ℝ≥0 using ne_top_of_lt hxy
  rcases eq_or_ne y ∞ with (rfl | hy)
  · simp only [top_rpow_of_pos h, ← coe_rpow_of_nonneg _ h.le, coe_lt_top]
  · lift y to ℝ≥0 using hy
    simp only [← coe_rpow_of_nonneg _ h.le, NNReal.rpow_lt_rpow (coe_lt_coe.1 hxy) h, coe_lt_coe]

theorem monotone_rpow_of_nonneg {z : ℝ} (h : 0 ≤ z) : Monotone fun x : ℝ≥0∞ => x ^ z :=
  h.eq_or_lt.elim (fun h0 => h0 ▸ by simp only [rpow_zero, monotone_const]) fun h0 =>
    (strictMono_rpow_of_pos h0).monotone

@[simps! apply]
def orderIsoRpow (y : ℝ) (hy : 0 < y) : ℝ≥0∞ ≃o ℝ≥0∞ :=
  (strictMono_rpow_of_pos hy).orderIsoOfRightInverse (fun x => x ^ y) (fun x => x ^ (1 / y))
    fun x => by
    dsimp
    rw [← rpow_mul, one_div_mul_cancel hy.ne.symm, rpow_one]

theorem orderIsoRpow_symm_apply (y : ℝ) (hy : 0 < y) :
    (orderIsoRpow y hy).symm = orderIsoRpow (1 / y) (one_div_pos.2 hy) := by
  simp only [orderIsoRpow, one_div_one_div]
  rfl

@[gcongr] theorem rpow_le_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x ≤ y) (h₂ : 0 ≤ z) : x ^ z ≤ y ^ z :=
  monotone_rpow_of_nonneg h₂ h₁

@[gcongr] theorem rpow_lt_rpow {x y : ℝ≥0∞} {z : ℝ} (h₁ : x < y) (h₂ : 0 < z) : x ^ z < y ^ z :=
  strictMono_rpow_of_pos h₂ h₁

theorem rpow_le_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z ≤ y ^ z ↔ x ≤ y :=
  (strictMono_rpow_of_pos hz).le_iff_le

theorem rpow_lt_rpow_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z < y ^ z ↔ x < y :=
  (strictMono_rpow_of_pos hz).lt_iff_lt

theorem le_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ z⁻¹ ↔ x ^ z ≤ y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul, @rpow_le_rpow_iff _ _ z⁻¹ (by simp [hz])]

theorem le_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ≤ y ^ (1 / z) ↔ x ^ z ≤ y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne']
  rw [rpow_mul, ← one_div, @rpow_le_rpow_iff _ _ (1 / z) (by simp [hz])]

theorem rpow_inv_lt_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ < y ↔ x < y ^ z := by
  simp only [← not_le, le_rpow_inv_iff hz]

theorem lt_rpow_inv_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ z⁻¹ ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, @rpow_lt_rpow_iff _ _ z⁻¹ (by simp [hz])]

theorem lt_rpow_one_div_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x < y ^ (1 / z) ↔ x ^ z < y := by
  nth_rw 1 [← rpow_one x]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z (ne_of_lt hz).symm]
  rw [rpow_mul, ← one_div, @rpow_lt_rpow_iff _ _ (1 / z) (by simp [hz])]

theorem rpow_inv_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ z⁻¹ ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 1 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ENNReal.rpow_le_rpow_iff (inv_pos.2 hz)]

theorem rpow_one_div_le_iff {x y : ℝ≥0∞} {z : ℝ} (hz : 0 < z) : x ^ (1 / z) ≤ y ↔ x ≤ y ^ z := by
  nth_rw 1 [← ENNReal.rpow_one y]
  nth_rw 2 [← @mul_inv_cancel₀ _ _ z hz.ne.symm]
  rw [ENNReal.rpow_mul, ← one_div, ENNReal.rpow_le_rpow_iff (one_div_pos.2 hz)]

theorem rpow_lt_rpow_of_exponent_lt {x : ℝ≥0∞} {y z : ℝ} (hx : 1 < x) (hx' : x ≠ ⊤) (hyz : y < z) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using hx'
  rw [one_lt_coe_iff] at hx
  simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
    NNReal.rpow_lt_rpow_of_exponent_lt hx hyz]

@[gcongr] theorem rpow_le_rpow_of_exponent_le {x : ℝ≥0∞} {y z : ℝ} (hx : 1 ≤ x) (hyz : y ≤ z) :
    x ^ y ≤ x ^ z := by
  cases x
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, top_rpow_of_neg, top_rpow_of_pos, le_refl] <;>
    linarith
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_rpow_of_exponent_le hx hyz]

theorem rpow_lt_rpow_of_exponent_gt {x : ℝ≥0∞} {y z : ℝ} (hx0 : 0 < x) (hx1 : x < 1) (hyz : z < y) :
    x ^ y < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx1 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx0 hx1
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx0), NNReal.rpow_lt_rpow_of_exponent_gt hx0 hx1 hyz]

theorem rpow_le_rpow_of_exponent_ge {x : ℝ≥0∞} {y z : ℝ} (hx1 : x ≤ 1) (hyz : z ≤ y) :
    x ^ y ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx1 coe_lt_top)
  by_cases h : x = 0
  · rcases lt_trichotomy y 0 with (Hy | Hy | Hy) <;>
    rcases lt_trichotomy z 0 with (Hz | Hz | Hz) <;>
    simp [Hy, Hz, h, zero_rpow_of_neg, zero_rpow_of_pos, le_refl] <;>
    linarith
  · rw [coe_le_one_iff] at hx1
    simp [← coe_rpow_of_ne_zero h,
      NNReal.rpow_le_rpow_of_exponent_ge (bot_lt_iff_ne_bot.mpr h) hx1 hyz]

theorem rpow_le_self_of_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (h_one_le : 1 ≤ z) : x ^ z ≤ x := by
  nth_rw 2 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_ge hx h_one_le

theorem le_rpow_self_of_one_le {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (h_one_le : 1 ≤ z) : x ≤ x ^ z := by
  nth_rw 1 [← ENNReal.rpow_one x]
  exact ENNReal.rpow_le_rpow_of_exponent_le hx h_one_le

theorem rpow_pos_of_nonneg {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hp_nonneg : 0 ≤ p) : 0 < x ^ p := by
  by_cases hp_zero : p = 0
  · simp [hp_zero, zero_lt_one]
  · rw [← Ne] at hp_zero
    have hp_pos := lt_of_le_of_ne hp_nonneg hp_zero.symm
    rw [← zero_rpow_of_pos hp_pos]
    exact rpow_lt_rpow hx_pos hp_pos

theorem rpow_pos {p : ℝ} {x : ℝ≥0∞} (hx_pos : 0 < x) (hx_ne_top : x ≠ ⊤) : 0 < x ^ p := by
  cases' lt_or_le 0 p with hp_pos hp_nonpos
  · exact rpow_pos_of_nonneg hx_pos (le_of_lt hp_pos)
  · rw [← neg_neg p, rpow_neg, ENNReal.inv_pos]
    exact rpow_ne_top_of_nonneg (Right.nonneg_neg_iff.mpr hp_nonpos) hx_ne_top

theorem rpow_lt_one {x : ℝ≥0∞} {z : ℝ} (hx : x < 1) (hz : 0 < z) : x ^ z < 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx le_top)
  simp only [coe_lt_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.rpow_lt_one hx hz]

theorem rpow_le_one {x : ℝ≥0∞} {z : ℝ} (hx : x ≤ 1) (hz : 0 ≤ z) : x ^ z ≤ 1 := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx coe_lt_top)
  simp only [coe_le_one_iff] at hx
  simp [← coe_rpow_of_nonneg _ hz, NNReal.rpow_le_one hx hz]

theorem rpow_lt_one_of_one_lt_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : z < 0) : x ^ z < 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_trans zero_lt_one hx)),
      NNReal.rpow_lt_one_of_one_lt_of_neg hx hz]

theorem rpow_le_one_of_one_le_of_neg {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : z < 0) : x ^ z ≤ 1 := by
  cases x
  · simp [top_rpow_of_neg hz, zero_lt_one]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_rpow_of_ne_zero (ne_of_gt (lt_of_lt_of_le zero_lt_one hx)),
      NNReal.rpow_le_one_of_one_le_of_nonpos hx (le_of_lt hz)]

theorem one_lt_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 < x) (hz : 0 < z) : 1 < x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [some_eq_coe, one_lt_coe_iff] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_lt_rpow hx hz]

theorem one_le_rpow {x : ℝ≥0∞} {z : ℝ} (hx : 1 ≤ x) (hz : 0 < z) : 1 ≤ x ^ z := by
  cases x
  · simp [top_rpow_of_pos hz]
  · simp only [one_le_coe_iff, some_eq_coe] at hx
    simp [← coe_rpow_of_nonneg _ (le_of_lt hz), NNReal.one_le_rpow hx (le_of_lt hz)]

theorem one_lt_rpow_of_pos_of_lt_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x < 1)
    (hz : z < 0) : 1 < x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_lt_of_le hx2 le_top)
  simp only [coe_lt_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1), NNReal.one_lt_rpow_of_pos_of_lt_one_of_neg hx1 hx2 hz]

theorem one_le_rpow_of_pos_of_le_one_of_neg {x : ℝ≥0∞} {z : ℝ} (hx1 : 0 < x) (hx2 : x ≤ 1)
    (hz : z < 0) : 1 ≤ x ^ z := by
  lift x to ℝ≥0 using ne_of_lt (lt_of_le_of_lt hx2 coe_lt_top)
  simp only [coe_le_one_iff, coe_pos] at hx1 hx2 ⊢
  simp [← coe_rpow_of_ne_zero (ne_of_gt hx1),
    NNReal.one_le_rpow_of_pos_of_le_one_of_nonpos hx1 hx2 (le_of_lt hz)]

@[simp] lemma toNNReal_rpow (x : ℝ≥0∞) (z : ℝ) : (x ^ z).toNNReal = x.toNNReal ^ z := by
  rcases lt_trichotomy z 0 with (H | H | H)
  · cases' x with x
    · simp [H, ne_of_lt]
    by_cases hx : x = 0
    · simp [hx, H, ne_of_lt]
    · simp [← coe_rpow_of_ne_zero hx]
  · simp [H]
  · cases x
    · simp [H, ne_of_gt]
    simp [← coe_rpow_of_nonneg _ (le_of_lt H)]

theorem toReal_rpow (x : ℝ≥0∞) (z : ℝ) : x.toReal ^ z = (x ^ z).toReal := by
  rw [ENNReal.toReal, ENNReal.toReal, ← NNReal.coe_rpow, ENNReal.toNNReal_rpow]

theorem ofReal_rpow_of_pos {x p : ℝ} (hx_pos : 0 < x) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  simp_rw [ENNReal.ofReal]
  rw [← coe_rpow_of_ne_zero, coe_inj, Real.toNNReal_rpow_of_nonneg hx_pos.le]
  simp [hx_pos]

theorem ofReal_rpow_of_nonneg {x p : ℝ} (hx_nonneg : 0 ≤ x) (hp_nonneg : 0 ≤ p) :
    ENNReal.ofReal x ^ p = ENNReal.ofReal (x ^ p) := by
  by_cases hp0 : p = 0
  · simp [hp0]
  by_cases hx0 : x = 0
  · rw [← Ne] at hp0
    have hp_pos : 0 < p := lt_of_le_of_ne hp_nonneg hp0.symm
    simp [hx0, hp_pos, hp_pos.ne.symm]
  rw [← Ne] at hx0
  exact ofReal_rpow_of_pos (hx_nonneg.lt_of_ne hx0.symm)

-- DISSOLVED: rpow_rpow_inv

-- DISSOLVED: rpow_inv_rpow

-- DISSOLVED: pow_rpow_inv_natCast

-- DISSOLVED: rpow_inv_natCast_pow

lemma rpow_natCast_mul (x : ℝ≥0∞) (n : ℕ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_mul_natCast (x : ℝ≥0∞) (y : ℝ) (n : ℕ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_natCast]

lemma rpow_intCast_mul (x : ℝ≥0∞) (n : ℤ) (z : ℝ) : x ^ (n * z) = (x ^ n) ^ z := by
  rw [rpow_mul, rpow_intCast]

lemma rpow_mul_intCast (x : ℝ≥0∞) (y : ℝ) (n : ℤ) : x ^ (y * n) = (x ^ y) ^ n := by
  rw [rpow_mul, rpow_intCast]

-- DISSOLVED: rpow_left_injective

-- DISSOLVED: rpow_left_surjective

-- DISSOLVED: rpow_left_bijective

end ENNReal
