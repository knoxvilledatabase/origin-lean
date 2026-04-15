/-
Extracted from LinearAlgebra/Lagrange.lean
Genuine: 11 of 11 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Lagrange interpolation

## Main definitions
* In everything that follows, `s : Finset ι` is a finite set of indices, with `v : ι → F` an
  indexing of the field over some type. We call the image of `v` on `s` the interpolation nodes,
  though strictly unique nodes are only defined when `v` is injective on `s`.
* `Lagrange.basisDivisor x y`, with `x y : F`. These are the normalised irreducible factors of
  the Lagrange basis polynomials. They evaluate to `1` at `x` and `0` at `y` when `x` and `y`
  are distinct.
* `Lagrange.basis v i` with `i : ι`: the Lagrange basis polynomial that evaluates to `1` at `v i`
  and `0` at `v j` for `i ≠ j`.
* `Lagrange.interpolate v r` where `r : ι → F` is a function from the fintype to the field: the
  Lagrange interpolant that evaluates to `r i` at `x i` for all `i : ι`. The `r i` are the _values_
  associated with the _nodes_ `x i`.
-/

open Polynomial

section PolynomialDetermination

namespace Polynomial

variable {R : Type*} [CommRing R] [IsDomain R] {f g : R[X]}

section Finset

open Function Fintype

open scoped Finset

variable (s : Finset R)

theorem eq_zero_of_degree_lt_of_eval_finset_eq_zero (degree_f_lt : f.degree < #s)
    (eval_f : ∀ x ∈ s, f.eval x = 0) : f = 0 := by
  rw [← mem_degreeLT] at degree_f_lt
  simp_rw [eval_eq_sum_degreeLTEquiv degree_f_lt] at eval_f
  rw [← degreeLTEquiv_eq_zero_iff_eq_zero degree_f_lt]
  exact
    Matrix.eq_zero_of_forall_index_sum_mul_pow_eq_zero
      (Injective.comp (Embedding.subtype _).inj' (equivFinOfCardEq (card_coe _)).symm.injective)
      fun _ => eval_f _ (Finset.coe_mem _)

theorem eq_of_degree_sub_lt_of_eval_finset_eq (degree_fg_lt : (f - g).degree < #s)
    (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_finset_eq (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ x ∈ s, f.eval x = g.eval x) : f = g := by
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt
  refine eq_of_degree_sub_lt_of_eval_finset_eq _ ?_ eval_fg
  rw [← mem_degreeLT]; exact Submodule.sub_mem _ degree_f_lt degree_g_lt

theorem eq_of_degree_le_of_eval_finset_eq
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ x ∈ s, f.eval x = g.eval x) :
    f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_finset_eq s
      (lt_of_lt_of_le (degree_sub_lt h_deg_eq hf hlc) h_deg_le) h_eval

end Finset

section Indexed

open Finset

variable {ι : Type*} {v : ι → R} (s : Finset ι)

theorem eq_zero_of_degree_lt_of_eval_index_eq_zero (hvs : Set.InjOn v s)
    (degree_f_lt : f.degree < #s) (eval_f : ∀ i ∈ s, f.eval (v i) = 0) : f = 0 := by
  classical
    rw [← card_image_of_injOn hvs] at degree_f_lt
    refine eq_zero_of_degree_lt_of_eval_finset_eq_zero _ degree_f_lt ?_
    intro x hx
    rcases mem_image.mp hx with ⟨_, hj, rfl⟩
    exact eval_f _ hj

theorem eq_of_degree_sub_lt_of_eval_index_eq (hvs : Set.InjOn v s)
    (degree_fg_lt : (f - g).degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) :
    f = g := by
  rw [← sub_eq_zero]
  refine eq_zero_of_degree_lt_of_eval_index_eq_zero _ hvs degree_fg_lt ?_
  simp_rw [eval_sub, sub_eq_zero]
  exact eval_fg

theorem eq_of_degrees_lt_of_eval_index_eq (hvs : Set.InjOn v s) (degree_f_lt : f.degree < #s)
    (degree_g_lt : g.degree < #s) (eval_fg : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  refine eq_of_degree_sub_lt_of_eval_index_eq _ hvs ?_ eval_fg
  rw [← mem_degreeLT] at degree_f_lt degree_g_lt ⊢
  exact Submodule.sub_mem _ degree_f_lt degree_g_lt

theorem eq_of_degree_le_of_eval_index_eq (hvs : Set.InjOn v s)
    (h_deg_le : f.degree ≤ #s)
    (h_deg_eq : f.degree = g.degree)
    (hlc : f.leadingCoeff = g.leadingCoeff)
    (h_eval : ∀ i ∈ s, f.eval (v i) = g.eval (v i)) : f = g := by
  rcases eq_or_ne f 0 with rfl | hf
  · rwa [degree_zero, eq_comm, degree_eq_bot, eq_comm] at h_deg_eq
  · exact eq_of_degree_sub_lt_of_eval_index_eq s hvs
      (lt_of_lt_of_le (degree_sub_lt h_deg_eq hf hlc) h_deg_le)
      h_eval

end Indexed

end Polynomial

end PolynomialDetermination

noncomputable section

namespace Lagrange

open Polynomial

section BasisDivisor

variable {F : Type*} [Field F]

variable {x y : F}

def basisDivisor (x y : F) : F[X] :=
  C (x - y)⁻¹ * (X - C y)

theorem basisDivisor_self : basisDivisor x x = 0 := by
  simp only [basisDivisor, sub_self, inv_zero, map_zero, zero_mul]

theorem basisDivisor_inj (hxy : basisDivisor x y = 0) : x = y := by
  simp_rw [basisDivisor, mul_eq_zero, X_sub_C_ne_zero, or_false, C_eq_zero, inv_eq_zero,
    sub_eq_zero] at hxy
  exact hxy
