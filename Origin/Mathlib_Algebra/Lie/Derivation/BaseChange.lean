/-
Extracted from Algebra/Lie/Derivation/BaseChange.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# LieDerivations of a Lie algebra created through BaseChange

When, given an `R`-algebra `A` and an `R`-Lie algebra `L` the (Lie algebra) basechange `A ⊗[R] L`,
both derivations of `A` and Lie derivations of `L` induce Lie derivations of `A ⊗[R] L`. Moreover,
both these procedures are Lie algebra homomorphisms themselves.


## Tags

lie algebra, extension of scalars, base change, derivation

-/

namespace Lie.Derivation

open TensorProduct

variable {R : Type*} [CommRing R]

variable {A : Type*} [CommRing A] [Algebra R A]

variable {L : Type*} [LieRing L] [LieAlgebra R L]

variable (L) in

def ofDerivation : Derivation R A A →ₗ⁅R⁆ LieDerivation R (A ⊗[R] L) (A ⊗[R] L) where
  toFun d :=
    { toFun := d.rTensor L
      map_add' := by simp
      map_smul' := by simp
      leibniz' x y := by
        simp only [LinearMap.coe_mk, AddHom.coe_mk]
        refine x.induction_on (by simp) (fun _ l ↦ ?_) (fun _ _ h1 h2 ↦ ?_)
        · refine y.induction_on (by simp) (fun _ l' ↦ ?_) (fun _ _ h1 h2 ↦ ?_)
          · simp [← lie_skew l' l, -lie_skew, add_tmul, tmul_neg]
          · simp [h1, h2, sub_add_sub_comm]
        · simp [h1, h2, sub_add_sub_comm] }
  map_add' _ _ := by ext; simp
  map_smul' _ _ := by ext; simp
  map_lie' {_ _} := by
    ext z
    refine z.induction_on (by simp) (by simp [sub_tmul]) (fun _ _ hx hy ↦ ?_)
    simp_all
    abel
