/-
Extracted from LinearAlgebra/Basis/Fin.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Bases indexed by `Fin`
-/

assert_not_exists Ordinal

noncomputable section

universe u

open Function Set Submodule Finsupp

variable {ι : Type*} {ι' : Type*} {R : Type*} {R₂ : Type*} {M : Type*} {M' : Type*}

namespace Module

open LinearMap

variable {v : ι → M}

variable [Ring R] [CommRing R₂] [AddCommGroup M]

variable [Module R M] [Module R₂ M]

variable {x y : M}

variable (b : Basis ι R M)

namespace Basis

section Fin

noncomputable def mkFinCons {n : ℕ} {N : Submodule R M} (y : M) (b : Basis (Fin n) R N)
    (hli : ∀ (c : R), ∀ x ∈ N, c • y + x = 0 → c = 0) (hsp : ∀ z : M, ∃ c : R, z + c • y ∈ N) :
    Basis (Fin (n + 1)) R M :=
  have span_b : Submodule.span R (Set.range (N.subtype ∘ b)) = N := by
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]
  Basis.mk (v := Fin.cons y (N.subtype ∘ b))
    ((b.linearIndependent.map' N.subtype (Submodule.ker_subtype _)).finCons' _ _
      (by
        intro c x hx hc
        rw [span_b] at hx
        exact hli c x hx hc))
    fun x _ => by
      rw [Fin.range_cons, Submodule.mem_span_insert', span_b]
      exact hsp x
