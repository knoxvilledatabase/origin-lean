/-
Extracted from Algebra/Module/Torsion/Free.lean
Genuine: 4 of 8 | Dissolved: 0 | Infrastructure: 4
-/
import Origin.Core

/-!
# Torsion-free modules

This files defines a torsion-free `R`-(semi)module `M` as a (semi)module where scalar multiplication
by a regular element `r : R` is injective as a map `M → M`.

In the case of a module (group over a ring), this is equivalent to saying that `r • m = 0` for
some `r : R`, `m : M` implies that `r` is a zero-divisor.
If furthermore the base ring is a domain, this is equivalent to the naïve
`r • m = 0 ↔ r = 0 ∨ m = 0` definition.
-/

open Module

variable {R S M N : Type*}

section Semiring

variable [Semiring R] [Semiring S]

section AddCommMonoid

variable [AddCommMonoid M] [Module R M] [Module S M] [AddCommMonoid N] [Module R N]
  {r : R} {m m₁ m₂ : M}

variable (R M) in

class Module.IsTorsionFree where
  isSMulRegular ⦃r : R⦄ : IsRegular r → IsSMulRegular M r

alias IsRegular.isSMulRegular := IsTorsionFree.isSMulRegular

-- INSTANCE (free from Core): :

-- INSTANCE (free from Core): :

lemma Function.Injective.moduleIsTorsionFree [IsTorsionFree R N] (f : M → N) (hf : f.Injective)
    (smul : ∀ (r : R) (m : M), f (r • m) = r • f m) : IsTorsionFree R M where
  isSMulRegular r hr m₁ m₂ hm := hf <| hr.isSMulRegular <| by simpa [smul] using congr(f $hm)

lemma Module.IsTorsionFree.comap [IsTorsionFree S M] (f : R → S)
    (isRegular : ∀ r, IsRegular r → IsRegular (f r)) (smul : ∀ (r : R) (m : M), f r • m = r • m) :
    IsTorsionFree R M where
  isSMulRegular r hr := (isRegular _ hr).isSMulRegular.of_map f (smul r)

-- INSTANCE (free from Core): IsAddTorsionFree.to_isTorsionFree_nat

-- INSTANCE (free from Core): Subsingleton.to_moduleIsTorsionFree

variable [IsTorsionFree R M]

variable (M) in

protected lemma IsRegular.smul_right_injective (hr : IsRegular r) : ((r • ·) : M → M).Injective :=
  hr.isSMulRegular
