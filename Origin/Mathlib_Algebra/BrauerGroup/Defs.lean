/-
Extracted from Algebra/BrauerGroup/Defs.lean
Genuine: 2 of 3 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Definition of Brauer group of a field K

We introduce the definition of Brauer group of a field K, which is the quotient of the set of
all finite-dimensional central simple algebras over K modulo the Brauer Equivalence where two
central simple algebras `A` and `B` are Brauer Equivalent if there exist `n, m ∈ ℕ+` such
that `Mₙ(A) ≃ₐ[K] Mₘ(B)`.

## TODOs
1. Prove that the Brauer group is an abelian group where multiplication is defined as tensor
   product.
2. Prove that the Brauer group is a functor from the category of fields to the category of groups.
3. Prove that over a field, being Brauer equivalent is the same as being Morita equivalent.

## References
* [Algebraic Number Theory, *J.W.S Cassels*][cassels1967algebraic]

## Tags
Brauer group, Central simple algebra, Galois Cohomology
-/

universe u v

structure CSA (K : Type u) [Field K] extends AlgCat.{v} K where
  /-- Any member of `CSA` is central. -/
  [isCentral : Algebra.IsCentral K carrier]
  /-- Any member of `CSA` is simple. -/
  [isSimple : IsSimpleRing carrier]
  /-- Any member of `CSA` is finite-dimensional. -/
  [fin_dim : FiniteDimensional K carrier]

variable {K : Type u} [Field K]

-- INSTANCE (free from Core): :

attribute [instance] CSA.isCentral CSA.isSimple CSA.fin_dim

abbrev IsBrauerEquivalent (A B : CSA K) : Prop :=
  ∃ n m : ℕ, n ≠ 0 ∧ m ≠ 0 ∧ (Nonempty <| Matrix (Fin n) (Fin n) A ≃ₐ[K] Matrix (Fin m) (Fin m) B)

namespace IsBrauerEquivalent
