/-
Extracted from Topology/Algebra/InfiniteSum/Ring.lean
Genuine: 22 | Conflates: 0 | Dissolved: 8 | Infrastructure: 1
-/
import Origin.Core
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.Ring.Basic

/-!
# Infinite sum in a ring

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
-/

open Filter Finset Function

variable {ι κ α : Type*}

section NonUnitalNonAssocSemiring

variable [NonUnitalNonAssocSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f : ι → α}
  {a₁ : α}

theorem HasSum.mul_left (a₂) (h : HasSum f a₁) : HasSum (fun i ↦ a₂ * f i) (a₂ * a₁) := by
  simpa only using h.map (AddMonoidHom.mulLeft a₂) (continuous_const.mul continuous_id)

theorem HasSum.mul_right (a₂) (hf : HasSum f a₁) : HasSum (fun i ↦ f i * a₂) (a₁ * a₂) := by
  simpa only using hf.map (AddMonoidHom.mulRight a₂) (continuous_id.mul continuous_const)

theorem Summable.mul_left (a) (hf : Summable f) : Summable fun i ↦ a * f i :=
  (hf.hasSum.mul_left _).summable

theorem Summable.mul_right (a) (hf : Summable f) : Summable fun i ↦ f i * a :=
  (hf.hasSum.mul_right _).summable

section tsum

variable [T2Space α]

theorem Summable.tsum_mul_left (a) (hf : Summable f) : ∑' i, a * f i = a * ∑' i, f i :=
  (hf.hasSum.mul_left _).tsum_eq

theorem Summable.tsum_mul_right (a) (hf : Summable f) : ∑' i, f i * a = (∑' i, f i) * a :=
  (hf.hasSum.mul_right _).tsum_eq

theorem Commute.tsum_right (a) (h : ∀ i, Commute a (f i)) : Commute a (∑' i, f i) := by
  classical
  by_cases hf : Summable f
  · exact (hf.tsum_mul_left a).symm.trans ((congr_arg _ <| funext h).trans (hf.tsum_mul_right a))
  · exact (tsum_eq_zero_of_not_summable hf).symm ▸ Commute.zero_right _

theorem Commute.tsum_left (a) (h : ∀ i, Commute (f i) a) : Commute (∑' i, f i) a :=
  (Commute.tsum_right _ fun i ↦ (h i).symm).symm

end tsum

end NonUnitalNonAssocSemiring

section DivisionSemiring

variable [DivisionSemiring α] [TopologicalSpace α] [TopologicalSemiring α] {f : ι → α} {a a₁ a₂ : α}

theorem HasSum.div_const (h : HasSum f a) (b : α) : HasSum (fun i ↦ f i / b) (a / b) := by
  simp only [div_eq_mul_inv, h.mul_right b⁻¹]

theorem Summable.div_const (h : Summable f) (b : α) : Summable fun i ↦ f i / b :=
  (h.hasSum.div_const _).summable

-- DISSOLVED: hasSum_mul_left_iff

-- DISSOLVED: hasSum_mul_right_iff

-- DISSOLVED: hasSum_div_const_iff

-- DISSOLVED: summable_mul_left_iff

-- DISSOLVED: summable_mul_right_iff

-- DISSOLVED: summable_div_const_iff

theorem tsum_mul_left [T2Space α] : ∑' x, a * f x = a * ∑' x, f x := by
  classical
  exact if hf : Summable f then hf.tsum_mul_left a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsum_eq_zero_of_not_summable hf,
              tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).mp hf), mul_zero]

theorem tsum_mul_right [T2Space α] : ∑' x, f x * a = (∑' x, f x) * a := by
  classical
  exact if hf : Summable f then hf.tsum_mul_right a
  else if ha : a = 0 then by simp [ha]
  else by rw [tsum_eq_zero_of_not_summable hf,
              tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).mp hf), zero_mul]

theorem tsum_div_const [T2Space α] : ∑' x, f x / a = (∑' x, f x) / a := by
  simpa only [div_eq_mul_inv] using tsum_mul_right

theorem HasSum.const_div (h :  HasSum (fun x ↦ 1 / f x) a) (b : α) :
    HasSum (fun i ↦ b / f i) (b * a) := by
  have := h.mul_left b
  simpa only [div_eq_mul_inv, one_mul] using this

theorem Summable.const_div (h : Summable (fun x ↦ 1 / f x)) (b : α) :
    Summable fun i ↦ b / f i :=
  (h.hasSum.const_div b).summable

-- DISSOLVED: hasSum_const_div_iff

-- DISSOLVED: summable_const_div_iff

end DivisionSemiring

/-!
### Multiplying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `fun x : ι × κ ↦ f x.1 * g x.2` is summable, since there is no way to
deduce this from the summabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `Analysis.Normed.Module.Basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/

section tsum_mul_tsum

variable [TopologicalSpace α] [T3Space α] [NonUnitalNonAssocSemiring α] [TopologicalSemiring α]
  {f : ι → α} {g : κ → α} {s t u : α}

theorem HasSum.mul_eq (hf : HasSum f s) (hg : HasSum g t)
    (hfg : HasSum (fun x : ι × κ ↦ f x.1 * g x.2) u) : s * t = u :=
  have key₁ : HasSum (fun i ↦ f i * t) (s * t) := hf.mul_right t
  have this : ∀ i : ι, HasSum (fun c : κ ↦ f i * g c) (f i * t) := fun i ↦ hg.mul_left (f i)
  have key₂ : HasSum (fun i ↦ f i * t) u := HasSum.prod_fiberwise hfg this
  key₁.unique key₂

theorem HasSum.mul (hf : HasSum f s) (hg : HasSum g t)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    HasSum (fun x : ι × κ ↦ f x.1 * g x.2) (s * t) :=
  let ⟨_u, hu⟩ := hfg
  (hf.mul_eq hg hu).symm ▸ hu

theorem tsum_mul_tsum (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ι × κ ↦ f x.1 * g x.2) :
    ((∑' x, f x) * ∑' y, g y) = ∑' z : ι × κ, f z.1 * g z.2 :=
  hf.hasSum.mul_eq hg.hasSum hfg.hasSum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `Finset.range (n+1)`
involving `Nat` subtraction.
In order to avoid `Nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`Finset` `Finset.antidiagonal n`.
This in fact allows us to generalize to any type satisfying `[Finset.HasAntidiagonal A]`
-/

section CauchyProduct

section HasAntidiagonal

variable {A : Type*} [AddCommMonoid A] [HasAntidiagonal A]

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : A → α}

theorem summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
    (Summable fun x : A × A ↦ f x.1 * g x.2) ↔
      Summable fun x : Σn : A, antidiagonal n ↦ f (x.2 : A × A).1 * g (x.2 : A × A).2 :=
  Finset.sigmaAntidiagonalEquivProd.summable_iff.symm

variable [T3Space α] [TopologicalSemiring α]

theorem summable_sum_mul_antidiagonal_of_summable_mul
    (h : Summable fun x : A × A ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  rw [summable_mul_prod_iff_summable_mul_sigma_antidiagonal] at h
  conv => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  exact h.sigma' fun n ↦ (hasSum_fintype _).summable

theorem tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : A × A ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ kl ∈ antidiagonal n, f kl.1 * g kl.2 := by
  conv_rhs => congr; ext; rw [← Finset.sum_finset_coe, ← tsum_fintype]
  rw [tsum_mul_tsum hf hg hfg, ← sigmaAntidiagonalEquivProd.tsum_eq (_ : A × A → α)]
  exact
    tsum_sigma' (fun n ↦ (hasSum_fintype _).summable)
      (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)

end HasAntidiagonal

section Nat

variable [TopologicalSpace α] [NonUnitalNonAssocSemiring α] {f g : ℕ → α}

variable [T3Space α] [TopologicalSemiring α]

theorem summable_sum_mul_range_of_summable_mul (h : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    Summable fun n ↦ ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact summable_sum_mul_antidiagonal_of_summable_mul h

theorem tsum_mul_tsum_eq_tsum_sum_range (hf : Summable f) (hg : Summable g)
    (hfg : Summable fun x : ℕ × ℕ ↦ f x.1 * g x.2) :
    ((∑' n, f n) * ∑' n, g n) = ∑' n, ∑ k ∈ range (n + 1), f k * g (n - k) := by
  simp_rw [← Nat.sum_antidiagonal_eq_sum_range_succ fun k l ↦ f k * g l]
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg

end Nat

end CauchyProduct
