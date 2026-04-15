/-
Extracted from Algebra/Polynomial/RingDivision.lean
Genuine: 22 of 30 | Dissolved: 7 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Div

/-!
# Theory of univariate polynomials

We prove basic results about univariate polynomials.

-/

noncomputable section

open Polynomial

open Finset

namespace Polynomial

universe u v w z

variable {R : Type u} {S : Type v} {T : Type w} {a b : R} {n : ℕ}

section CommRing

variable [CommRing R] {p q : R[X]}

section

variable [Semiring S]

-- DISSOLVED: natDegree_pos_of_aeval_root

-- DISSOLVED: degree_pos_of_aeval_root

end

theorem smul_modByMonic (c : R) (p : R[X]) : c • p %ₘ q = c • (p %ₘ q) := by
  by_cases hq : q.Monic
  · cases' subsingleton_or_nontrivial R with hR hR
    · simp only [eq_iff_true_of_subsingleton]
    · exact
      (div_modByMonic_unique (c • (p /ₘ q)) (c • (p %ₘ q)) hq
          ⟨by rw [mul_smul_comm, ← smul_add, modByMonic_add_div p hq],
            (degree_smul_le _ _).trans_lt (degree_modByMonic_lt _ hq)⟩).2
  · simp_rw [modByMonic_eq_of_not_monic _ hq]

@[simps]
def modByMonicHom (q : R[X]) : R[X] →ₗ[R] R[X] where
  toFun p := p %ₘ q
  map_add' := add_modByMonic
  map_smul' := smul_modByMonic

theorem mem_ker_modByMonic (hq : q.Monic) {p : R[X]} :
    p ∈ LinearMap.ker (modByMonicHom q) ↔ q ∣ p :=
  LinearMap.mem_ker.trans (modByMonic_eq_zero_iff_dvd hq)

@[simp]
theorem ker_modByMonicHom (hq : q.Monic) :
    LinearMap.ker (Polynomial.modByMonicHom q) = (Ideal.span {q}).restrictScalars R :=
  Submodule.ext fun _ => (mem_ker_modByMonic hq).trans Ideal.mem_span_singleton.symm

section

variable [Ring S]

theorem aeval_modByMonic_eq_self_of_root [Algebra R S] {p q : R[X]} (hq : q.Monic) {x : S}
    (hx : aeval x q = 0) : aeval x (p %ₘ q) = aeval x p := by
    --`eval₂_modByMonic_eq_self_of_root` doesn't work here as it needs commutativity
  rw [modByMonic_eq_sub_mul_div p hq, _root_.map_sub, _root_.map_mul, hx, zero_mul,
    sub_zero]

end

end CommRing

section NoZeroDivisors

variable [Semiring R] [NoZeroDivisors R] {p q : R[X]}

theorem trailingDegree_mul : (p * q).trailingDegree = p.trailingDegree + q.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp, zero_mul, trailingDegree_zero, top_add]
  by_cases hq : q = 0
  · rw [hq, mul_zero, trailingDegree_zero, add_top]
  · rw [trailingDegree_eq_natTrailingDegree hp, trailingDegree_eq_natTrailingDegree hq,
    trailingDegree_eq_natTrailingDegree (mul_ne_zero hp hq), natTrailingDegree_mul hp hq]
    apply WithTop.coe_add

end NoZeroDivisors

section CommRing

variable [CommRing R]

theorem rootMultiplicity_eq_rootMultiplicity {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).rootMultiplicity 0 := by
  classical
  simp_rw [rootMultiplicity_eq_multiplicity, comp_X_add_C_eq_zero_iff]
  congr 1
  rw [C_0, sub_zero]
  convert (multiplicity_map_eq <| algEquivAevalXAddC t).symm using 2
  simp [C_eq_algebraMap]

theorem rootMultiplicity_eq_natTrailingDegree {p : R[X]} {t : R} :
    p.rootMultiplicity t = (p.comp (X + C t)).natTrailingDegree :=
  rootMultiplicity_eq_rootMultiplicity.trans rootMultiplicity_eq_natTrailingDegree'

section nonZeroDivisors

open scoped nonZeroDivisors

theorem Monic.mem_nonZeroDivisors {p : R[X]} (h : p.Monic) : p ∈ R[X]⁰ :=
  mem_nonZeroDivisors_iff.2 fun _ hx ↦ (mul_left_eq_zero_iff h).1 hx

theorem mem_nonZeroDivisors_of_leadingCoeff {p : R[X]} (h : p.leadingCoeff ∈ R⁰) : p ∈ R[X]⁰ := by
  refine mem_nonZeroDivisors_iff.2 fun x hx ↦ leadingCoeff_eq_zero.1 ?_
  by_contra hx'
  rw [← mul_right_mem_nonZeroDivisors_eq_zero_iff h] at hx'
  simp only [← leadingCoeff_mul' hx', hx, leadingCoeff_zero, not_true] at hx'

end nonZeroDivisors

-- DISSOLVED: rootMultiplicity_mul_X_sub_C_pow

theorem rootMultiplicity_X_sub_C_pow [Nontrivial R] (a : R) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n) = n := by
  have := rootMultiplicity_mul_X_sub_C_pow (a := a) (n := n) C.map_one_ne_zero
  rwa [rootMultiplicity_C, map_one, one_mul, zero_add] at this

theorem rootMultiplicity_X_sub_C_self [Nontrivial R] {x : R} :
    rootMultiplicity x (X - C x) = 1 :=
  pow_one (X - C x) ▸ rootMultiplicity_X_sub_C_pow x 1

theorem rootMultiplicity_X_sub_C [Nontrivial R] [DecidableEq R] {x y : R} :
    rootMultiplicity x (X - C y) = if x = y then 1 else 0 := by
  split_ifs with hxy
  · rw [hxy]
    exact rootMultiplicity_X_sub_C_self
  exact rootMultiplicity_eq_zero (mt root_X_sub_C.mp (Ne.symm hxy))

-- DISSOLVED: rootMultiplicity_mul'

theorem Monic.neg_one_pow_natDegree_mul_comp_neg_X {p : R[X]} (hp : p.Monic) :
    ((-1) ^ p.natDegree * p.comp (-X)).Monic := by
  simp only [Monic]
  calc
    ((-1) ^ p.natDegree * p.comp (-X)).leadingCoeff =
        (p.comp (-X) * C ((-1) ^ p.natDegree)).leadingCoeff := by
      simp [mul_comm]
    _ = 1 := by
      apply monic_mul_C_of_leadingCoeff_mul_eq_one
      simp [← pow_add, hp]

variable [IsDomain R] {p q : R[X]}

theorem degree_eq_degree_of_associated (h : Associated p q) : degree p = degree q := by
  let ⟨u, hu⟩ := h
  simp [hu.symm]

theorem prime_X_sub_C (r : R) : Prime (X - C r) :=
  ⟨X_sub_C_ne_zero r, not_isUnit_X_sub_C r, fun _ _ => by
    simp_rw [dvd_iff_isRoot, IsRoot.def, eval_mul, mul_eq_zero]
    exact id⟩

theorem prime_X : Prime (X : R[X]) := by
  convert prime_X_sub_C (0 : R)
  simp

theorem Monic.prime_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Prime p :=
  have : p = X - C (-p.coeff 0) := by simpa [hm.leadingCoeff] using eq_X_add_C_of_degree_eq_one hp1
  this.symm ▸ prime_X_sub_C _

theorem irreducible_X_sub_C (r : R) : Irreducible (X - C r) :=
  (prime_X_sub_C r).irreducible

theorem irreducible_X : Irreducible (X : R[X]) :=
  Prime.irreducible prime_X

theorem Monic.irreducible_of_degree_eq_one (hp1 : degree p = 1) (hm : Monic p) : Irreducible p :=
  (hm.prime_of_degree_eq_one hp1).irreducible

-- DISSOLVED: aeval_ne_zero_of_isCoprime

theorem isCoprime_X_sub_C_of_isUnit_sub {R} [CommRing R] {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (X - C a) (X - C b) :=
  ⟨-C h.unit⁻¹.val, C h.unit⁻¹.val, by
    rw [neg_mul_comm, ← left_distrib, neg_add_eq_sub, sub_sub_sub_cancel_left, ← C_sub, ← C_mul]
    rw [← C_1]
    congr
    exact h.val_inv_mul⟩

theorem pairwise_coprime_X_sub_C {K} [Field K] {I : Type v} {s : I → K} (H : Function.Injective s) :
    Pairwise (IsCoprime on fun i : I => X - C (s i)) := fun _ _ hij =>
  isCoprime_X_sub_C_of_isUnit_sub (sub_ne_zero_of_ne <| H.ne hij).isUnit

-- DISSOLVED: rootMultiplicity_mul

open Multiset in

set_option linter.unusedVariables false in

-- DISSOLVED: exists_multiset_roots

termination_by p => natDegree p

decreasing_by {

  simp_wf

  apply (Nat.cast_lt (α := WithBot ℕ)).mp

  simp only [degree_eq_natDegree hp, degree_eq_natDegree hd0] at wf

  assumption}

end CommRing

end Polynomial
