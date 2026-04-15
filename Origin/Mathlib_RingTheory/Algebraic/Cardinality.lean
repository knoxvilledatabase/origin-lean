/-
Extracted from RingTheory/Algebraic/Cardinality.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cardinality of algebraic extensions

This file contains results on cardinality of algebraic extensions.
-/

universe u v

open Cardinal Module

open scoped Polynomial

namespace Algebra.IsAlgebraic

variable (R : Type u) [CommRing R] [IsDomain R] (L : Type v) [CommRing L] [IsDomain L] [Algebra R L]

variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

theorem lift_cardinalMk_le_sigma_polynomial :
    lift.{u} #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  have := @lift_mk_le_lift_mk_of_injective L (Σ p : R[X], {x : L | x ∈ p.aroots L})
    (fun x : L =>
      let p := Classical.indefiniteDescription _ (Algebra.IsAlgebraic.isAlgebraic x)
      ⟨p.1, x, by
        dsimp
        have := (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective R L)).2 p.2.1
        rw [Polynomial.mem_roots this, Polynomial.IsRoot, Polynomial.eval_map,
          ← Polynomial.aeval_def, p.2.2]⟩)
    fun x y => by
      intro h
      simp only [Set.coe_setOf, ne_eq, Set.mem_setOf_eq, Sigma.mk.inj_iff] at h
      refine (Subtype.heq_iff_coe_eq ?_).1 h.2
      simp only [h.1, forall_true_iff]
  rwa [lift_umax, lift_id'.{v}] at this

variable (L : Type u) [CommRing L] [IsDomain L] [Algebra R L]

variable [IsTorsionFree R L] [Algebra.IsAlgebraic R L]

theorem cardinalMk_le_sigma_polynomial :
    #L ≤ #(Σ p : R[X], { x : L // x ∈ p.aroots L }) := by
  simpa only [lift_id] using lift_cardinalMk_le_sigma_polynomial R L
