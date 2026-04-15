/-
Extracted from ModelTheory/Arithmetic/Presburger/Semilinear/Defs.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Linear and semilinear sets

This file defines linear and semilinear sets. In an `AddCommMonoid`, a linear set is a coset of a
finitely generated additive submonoid, and a semilinear set is a finite union of linear sets.

We prove that semilinear sets are closed under union, projection, set addition and additive closure.
We also prove that any semilinear set can be decomposed into a finite union of proper linear sets,
which are linear sets with linearly independent submonoid generators (periods).

## Main Definitions

- `IsLinearSet`: a set is linear if it is a coset of a finitely generated additive submonoid.
- `IsSemilinearSet`: a set is semilinear if it is a finite union of linear sets.
- `IsProperLinearSet`: a linear set is proper if its submonoid generators (periods) are linearly
  independent.
- `IsProperSemilinearSet`: a semilinear set is proper if it is a finite union of proper linear sets.

## Main Results

- `IsSemilinearSet` is closed under union, projection, set addition and additive closure.
- `IsSemilinearSet.isProperSemilinearSet`: every semilinear set is a finite union of proper linear
  sets.
- `Nat.isSemilinearSet_iff_ultimately_periodic`: A set of `ℕ` is semilinear if and only if it is
  ultimately periodic, i.e. periodic after some number `k`.

## Naming convention

`IsSemilinearSet.proj` projects a semilinear set of `ι ⊕ κ → M` to `ι → M` by taking `Sum.inl` on
the index. It is a special case of `IsSemilinearSet.image`, and is useful in proving semilinearity
of sets in form `{ x | ∃ y, p x y }`.

## References

* [Seymour Ginsburg and Edwin H. Spanier, *Bounded ALGOL-Like Languages*][ginsburg1964]
* [Samuel Eilenberg and M. P. Schützenberger, *Rational Sets in Commutative Monoids*][eilenberg1969]
-/

variable {M N ι κ F : Type*} [AddCommMonoid M] [AddCommMonoid N]
  [FunLike F M N] [AddMonoidHomClass F M N] {a : M} {s s₁ s₂ : Set M}

open Set Pointwise AddSubmonoid

def IsLinearSet (s : Set M) : Prop :=
  ∃ (a : M) (t : Set M), t.Finite ∧ s = a +ᵥ (closure t : Set M)

theorem isLinearSet_iff :
    IsLinearSet s ↔ ∃ (a : M) (t : Finset M), s = a +ᵥ (closure (t : Set M) : Set M) := by
  simp [IsLinearSet, Finset.exists]
