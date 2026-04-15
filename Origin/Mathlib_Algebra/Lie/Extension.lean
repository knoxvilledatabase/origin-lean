/-
Extracted from Algebra/Lie/Extension.lean
Genuine: 4 of 6 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Extensions of Lie algebras
This file defines extensions of Lie algebras, given by short exact sequences of Lie algebra
homomorphisms. They are implemented in two ways: `IsExtension` is a `Prop`-valued class taking two
homomorphisms as parameters, and `Extension` is a structure that includes the middle Lie algebra.

Because our sign convention for differentials is opposite that of Chevalley-Eilenberg, there is a
change of signs in the "action" part of the Lie bracket.

## Main definitions
* `LieAlgebra.IsExtension`: A `Prop`-valued class characterizing an extension of Lie algebras.
* `LieAlgebra.Extension`: A bundled structure giving an extension of Lie algebras.
* `LieAlgebra.IsExtension.extension`: A function that builds the bundled structure from the class.
* `LieAlgebra.ofTwoCocycle`: The Lie algebra built from a direct product, but whose bracket product
  is sheared by a 2-cocycle.
* `LieAlgebra.Extension.ofTwoCocycle`: The Lie algebra extension constructed from a 2-cocycle.
* `LieAlgebra.Extension.ringModuleOf`: Given an extension whose kernel is abelian, we obtain a Lie
  action of the target on the kernel.
* `LieAlgebra.Extension.twoCocycle`: The 2-cocycle attached to an extension with a linear section.
* `LieAlgebra.Extension.oneCochainOfTwoSplitting`: A 1-cochain attached to a pair of linear sections
  of an extension.

## TODO
* `IsCentral` - central extensions
* `Equiv` - equivalence of extensions

## References
* [Chevalley, Eilenberg, *Cohomology Theory of Lie Groups and Lie
  Algebras*](chevalley_eilenberg_1948)
* [N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 1--3*](bourbaki1975)

-/

open Function

namespace LieAlgebra

variable {R N L M : Type*}

section IsExtension

variable [CommRing R] [LieRing L] [LieAlgebra R L] [LieRing N] [LieAlgebra R N] [LieRing M]
  [LieAlgebra R M]

class IsExtension (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) : Prop where
  ker_eq_bot : i.ker = ⊥
  range_eq_top : p.range = ⊤
  exact : i.range = p.ker

lemma _root_.LieHom.range_eq_ker_iff (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) :
    i.range = p.ker ↔ Exact i p :=
  ⟨fun h x ↦ by simp [← LieHom.coe_range, h], fun h ↦ (p.ker.toLieSubalgebra.ext i.range h).symm⟩

def IsExtension.kerEquivRange (i : N →ₗ⁅R⁆ L) (p : L →ₗ⁅R⁆ M) [IsExtension i p] :
    p.ker ≃ₗ[R] i.range :=
  .ofEq (R := R) (M := L) p.ker i.range <| by simp [exact (i := i) (p := p)]

variable (R N M) in

structure Extension where
  /-- The middle object in the sequence. -/
  L : Type*
  /-- `L` is a Lie ring. -/
  instLieRing : LieRing L
  /-- `L` is a Lie algebra over `R`. -/
  instLieAlgebra : LieAlgebra R L
  /-- The inclusion homomorphism `N →ₗ⁅R⁆ L` -/
  incl : N →ₗ⁅R⁆ L
  /-- The projection homomorphism `L →ₗ⁅R⁆ M` -/
  proj : L →ₗ⁅R⁆ M
  IsExtension : IsExtension incl proj

-- INSTANCE (free from Core): (E

-- INSTANCE (free from Core): (E
