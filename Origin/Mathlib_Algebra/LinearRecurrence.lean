/-
Extracted from Algebra/LinearRecurrence.lean
Genuine: 13 of 15 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Linear recurrence

Informally, a "linear recurrence" is an assertion of the form
`∀ n : ℕ, u (n + d) = a 0 * u n + a 1 * u (n+1) + ... + a (d-1) * u (n+d-1)`,
where `u` is a sequence, `d` is the *order* of the recurrence and the `a i`
are its *coefficients*.

In this file, we define the structure `LinearRecurrence` so that
`LinearRecurrence.mk d a` represents the above relation, and we call
a sequence `u` which verifies it a *solution* of the linear recurrence.

We prove a few basic lemmas about this concept, such as :

* the space of solutions is a submodule of `(ℕ → α)` (i.e a vector space if `α`
  is a field)
* the function that maps a solution `u` to its first `d` terms builds a `LinearEquiv`
  between the solution space and `Fin d → α`, aka `α ^ d`. As a consequence, two
  solutions are equal if and only if their first `d` terms are equal.
* a geometric sequence `q ^ n` is solution iff `q` is a root of a particular polynomial,
  which we call the *characteristic polynomial* of the recurrence

Of course, although we can inductively generate solutions (cf `mkSol`), the
interesting part would be to determine closed-forms for the solutions.
This is currently *not implemented*, as we are waiting for definition and
properties of eigenvalues and eigenvectors.

-/

noncomputable section

open Finset

open Polynomial

structure LinearRecurrence (R : Type*) [CommSemiring R] where
  /-- Order of the linear recurrence -/
  order : ℕ
  /-- Coefficients of the linear recurrence -/
  coeffs : Fin order → R

-- INSTANCE (free from Core): (R

namespace LinearRecurrence

section CommSemiring

variable {R : Type*} [CommSemiring R] (E : LinearRecurrence R)

def IsSolution (u : ℕ → R) :=
  ∀ n, u (n + E.order) = ∑ i, E.coeffs i * u (n + i)

def mkSol (init : Fin E.order → R) : ℕ → R
  | n =>
    if h : n < E.order then init ⟨n, h⟩
    else
      ∑ k : Fin E.order,
        have _ : n - E.order + k < n := by lia
        E.coeffs k * mkSol init (n - E.order + k)

theorem is_sol_mkSol (init : Fin E.order → R) : E.IsSolution (E.mkSol init) := by
  intro n
  rw [mkSol]
  simp

theorem mkSol_eq_init (init : Fin E.order → R) : ∀ n : Fin E.order, E.mkSol init n = init n := by
  intro n
  rw [mkSol]
  simp only [n.is_lt, dif_pos, Fin.mk_val]

theorem eq_mk_of_is_sol_of_eq_init {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : ∀ n, u n = E.mkSol init n := by
  intro n
  rw [mkSol]
  split_ifs with h'
  · exact mod_cast heq ⟨n, h'⟩
  · dsimp only
    rw [← tsub_add_cancel_of_le (le_of_not_gt h'), h (n - E.order)]
    congr with k
    rw [eq_mk_of_is_sol_of_eq_init h heq (n - E.order + k)]
    simp

theorem eq_mk_of_is_sol_of_eq_init' {u : ℕ → R} {init : Fin E.order → R} (h : E.IsSolution u)
    (heq : ∀ n : Fin E.order, u n = init n) : u = E.mkSol init :=
  funext (E.eq_mk_of_is_sol_of_eq_init h heq)

def solSpace : Submodule R (ℕ → R) where
  carrier := { u | E.IsSolution u }
  zero_mem' n := by simp
  add_mem' {u v} hu hv n := by simp [mul_add, sum_add_distrib, hu n, hv n]
  smul_mem' a u hu n := by simp [hu n, mul_sum]; ac_rfl

def toInit : E.solSpace ≃ₗ[R] Fin E.order → R where
  toFun u x := (u : ℕ → R) x
  map_add' u v := by
    ext
    simp
  map_smul' a u := by
    ext
    simp
  invFun u := ⟨E.mkSol u, E.is_sol_mkSol u⟩
  left_inv u := by ext n; symm; apply E.eq_mk_of_is_sol_of_eq_init u.2; intro k; rfl
  right_inv u := funext_iff.mpr fun n ↦ E.mkSol_eq_init u n

theorem sol_eq_of_eq_init (u v : ℕ → R) (hu : E.IsSolution u) (hv : E.IsSolution v) :
    u = v ↔ Set.EqOn u v ↑(range E.order) := by
  refine Iff.intro (fun h x _ ↦ h ▸ rfl) ?_
  intro h
  set u' : ↥E.solSpace := ⟨u, hu⟩
  set v' : ↥E.solSpace := ⟨v, hv⟩
  change u'.val = v'.val
  suffices h' : u' = v' from h' ▸ rfl
  rw [← E.toInit.toEquiv.apply_eq_iff_eq, LinearEquiv.coe_toEquiv]
  ext x
  exact mod_cast h (mem_range.mpr x.2)

/-! `E.tupleSucc` maps `![s₀, s₁, ..., sₙ]` to `![s₁, ..., sₙ, ∑ (E.coeffs i) * sᵢ]`,
where `n := E.order`. This operation is quite useful for determining closed-form
solutions of `E`. -/

def tupleSucc : (Fin E.order → R) →ₗ[R] Fin E.order → R where
  toFun X i := if h : (i : ℕ) + 1 < E.order then X ⟨i + 1, h⟩ else ∑ i, E.coeffs i * X i
  map_add' x y := by
    ext i
    split_ifs with h <;> simp [h, mul_add, sum_add_distrib]
  map_smul' x y := by
    ext i
    split_ifs with h <;>
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, h, ↓reduceDIte, mul_sum]
    exact sum_congr rfl fun x _ ↦ by ac_rfl

end CommSemiring

section StrongRankCondition

variable {R : Type*} [CommRing R] [StrongRankCondition R] (E : LinearRecurrence R)

theorem solSpace_rank : Module.rank R E.solSpace = E.order :=
  letI := nontrivial_of_invariantBasisNumber R
  @rank_fin_fun R _ _ E.order ▸ E.toInit.rank_eq

end StrongRankCondition

section CommRing

variable {R : Type*} [CommRing R] (E : LinearRecurrence R)

def charPoly : R[X] :=
  Polynomial.monomial E.order 1 - ∑ i : Fin E.order, Polynomial.monomial i (E.coeffs i)
