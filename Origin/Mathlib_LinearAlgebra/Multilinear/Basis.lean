/-
Extracted from LinearAlgebra/Multilinear/Basis.lean
Genuine: 2 | Conflates: 0 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core
import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Multilinear maps in relation to bases.

This file proves lemmas about the action of multilinear maps on basis vectors.

## TODO

 * Refactor the proofs in terms of bases of tensor products, once there is an equivalent of
   `Basis.tensorProduct` for `PiTensorProduct`.

-/

open MultilinearMap

variable {R : Type*} {ι : Type*} {n : ℕ} {M : Fin n → Type*} {M₂ : Type*} {M₃ : Type*}

variable [CommSemiring R] [AddCommMonoid M₂] [AddCommMonoid M₃] [∀ i, AddCommMonoid (M i)]

variable [∀ i, Module R (M i)] [Module R M₂] [Module R M₃]

theorem Basis.ext_multilinear_fin {f g : MultilinearMap R M M₂} {ι₁ : Fin n → Type*}
    (e : ∀ i, Basis (ι₁ i) R (M i))
    (h : ∀ v : ∀ i, ι₁ i, (f fun i => e i (v i)) = g fun i => e i (v i)) : f = g := by
  induction' n with m hm
  · ext x
    convert h finZeroElim
  · apply Function.LeftInverse.injective uncurry_curryLeft
    refine Basis.ext (e 0) ?_
    intro i
    apply hm (Fin.tail e)
    intro j
    convert h (Fin.cons i j)
    iterate 2
      rw [curryLeft_apply]
      congr 1 with x
      refine Fin.cases rfl (fun x => ?_) x
      dsimp [Fin.tail]
      rw [Fin.cons_succ, Fin.cons_succ]

theorem Basis.ext_multilinear [Finite ι] {f g : MultilinearMap R (fun _ : ι => M₂) M₃} {ι₁ : Type*}
    (e : Basis ι₁ R M₂) (h : ∀ v : ι → ι₁, (f fun i => e (v i)) = g fun i => e (v i)) : f = g := by
  cases nonempty_fintype ι
  exact
    (domDomCongr_eq_iff (Fintype.equivFin ι) f g).mp
      (Basis.ext_multilinear_fin (fun _ => e) fun i => h (i ∘ _))
