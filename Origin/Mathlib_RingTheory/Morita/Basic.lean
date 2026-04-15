/-
Extracted from RingTheory/Morita/Basic.lean
Genuine: 9 of 11 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Morita equivalence

Two `R`-algebras `A` and `B` are Morita equivalent if the categories of modules over `A` and
`B` are `R`-linearly equivalent. In this file, we prove that Morita equivalence is an equivalence
relation and that isomorphic algebras are Morita equivalent.

## Main definitions

- `MoritaEquivalence R A B`: a structure containing an `R`-linear equivalence of categories between
  the module categories of `A` and `B`.
- `IsMoritaEquivalent R A B`: a predicate asserting that `R`-algebras `A` and `B` are Morita
  equivalent.

## TODO

- For any ring `R`, `R` and `Matₙ(R)` are Morita equivalent.
- Morita equivalence in terms of projective generators.
- Morita equivalence in terms of full idempotents.
- Morita equivalence in terms of existence of an invertible bimodule.
- If `R ≈ S`, then `R` is simple iff `S` is simple.

## References

* [Nathan Jacobson, *Basic Algebra II*][jacobson1989]

## Tags

Morita Equivalence, Category Theory, Noncommutative Ring, Module Theory

-/

universe u₀ u₁ u₂ u₃

open CategoryTheory

variable (R : Type u₀) [CommSemiring R]

open scoped ModuleCat.Algebra

structure MoritaEquivalence
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] where
  /-- The underlying equivalence of categories -/
  eqv : ModuleCat.{max u₁ u₂} A ≌ ModuleCat.{max u₁ u₂} B
  linear : eqv.functor.Linear R := by infer_instance

namespace MoritaEquivalence

attribute [instance] MoritaEquivalence.linear

-- INSTANCE (free from Core): {A

def refl (A : Type u₁) [Ring A] [Algebra R A] : MoritaEquivalence R A A where
  eqv := CategoryTheory.Equivalence.refl
  linear := Functor.instLinearId

def symm {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (e : MoritaEquivalence R A B) : MoritaEquivalence R B A where
  eqv := e.eqv.symm
  linear := e.eqv.inverseLinear R

def trans {A B C : Type u₁}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] [Ring C] [Algebra R C]
    (e : MoritaEquivalence R A B) (e' : MoritaEquivalence R B C) :
    MoritaEquivalence R A C where
  eqv := e.eqv.trans e'.eqv
  linear := e.eqv.functor.instLinearComp e'.eqv.functor

variable {R} in

noncomputable def ofAlgEquiv {A : Type u₁} {B : Type u₂}
    [Ring A] [Algebra R A] [Ring B] [Algebra R B] (f : A ≃ₐ[R] B) :
    MoritaEquivalence R A B where
  eqv := ModuleCat.restrictScalarsEquivalenceOfRingEquiv f.symm.toRingEquiv
  linear := ModuleCat.Algebra.restrictScalarsEquivalenceOfRingEquiv_linear f.symm

end MoritaEquivalence

structure IsMoritaEquivalent
    (A : Type u₁) [Ring A] [Algebra R A]
    (B : Type u₂) [Ring B] [Algebra R B] : Prop where
  cond : Nonempty <| MoritaEquivalence R A B

namespace IsMoritaEquivalent

lemma refl (A : Type u₁) [Ring A] [Algebra R A] : IsMoritaEquivalent R A A where
  cond := ⟨.refl R A⟩

lemma trans {A B C : Type u₁} [Ring A] [Ring B] [Ring C] [Algebra R A] [Algebra R B] [Algebra R C]
    (h : IsMoritaEquivalent R A B) (h' : IsMoritaEquivalent R B C) :
    IsMoritaEquivalent R A C where
  cond := Nonempty.map2 (.trans R) h.cond h'.cond

lemma of_algEquiv {A : Type u₁} [Ring A] [Algebra R A] {B : Type u₂} [Ring B] [Algebra R B]
    (f : A ≃ₐ[R] B) : IsMoritaEquivalent R A B where
  cond := ⟨.ofAlgEquiv f⟩

end IsMoritaEquivalent
