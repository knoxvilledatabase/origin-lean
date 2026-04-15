/-
Extracted from Analysis/CStarAlgebra/Module/Defs.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Hilbert C⋆-modules

A Hilbert C⋆-module is a complex module `E` together with a right `A`-module structure, where `A`
is a C⋆-algebra, and with an `A`-valued inner product. This inner product satisfies the
Cauchy-Schwarz inequality, and induces a norm that makes `E` a normed vector space over `ℂ`.

## Main declarations

+ `CStarModule`: The class containing the Hilbert C⋆-module structure
+ `CStarModule.normedSpaceCore`: The proof that a Hilbert C⋆-module is a normed vector
  space. This can be used with `NormedAddCommGroup.ofCore` and `NormedSpace.ofCore` to create
  the relevant instances on a type of interest.
+ `CStarModule.inner_mul_inner_swap_le`: The statement that
  `⟪y, x⟫ * ⟪x, y⟫ ≤ ‖x‖ ^ 2 • ⟪y, y⟫`, which can be viewed as a version of the Cauchy-Schwarz
  inequality for Hilbert C⋆-modules.
+ `CStarModule.norm_inner_le`, which states that `‖⟪x, y⟫‖ ≤ ‖x‖ * ‖y‖`, i.e. the
  Cauchy-Schwarz inequality.

## Implementation notes

The class `CStarModule A E` requires `E` to already have a `Norm E` instance on it, but
no other norm-related instances. We then include the fact that this norm agrees with the norm
induced by the inner product among the axioms of the class. Furthermore, instead of registering
`NormedAddCommGroup E` and `NormedSpace ℂ E` instances (which might already be present on the type,
and which would send the type class search algorithm on a chase for `A`), we provide a
`NormedSpace.Core` structure which enables downstream users of the class to easily register
these instances themselves on a particular type.

Although the `Norm` is passed as a parameter, it almost never coincides with the norm on the
underlying type, unless that it is a purpose built type, as with the *standard Hilbert C⋆-module*.
However, with generic types already equipped with a norm, the norm as a Hilbert C⋆-module almost
never coincides with the norm on the underlying type. The two notable exceptions to this are when
we view `A` as a C⋆-module over itself, or when `A := ℂ`.  For this reason we will later use the
type synonym `WithCStarModule`.

As an example of just how different the norm can be, consider `CStarModule`s `E` and `F` over `A`.
One would like to put a `CStarModule` structure on (a type synonym of) `E × F`, where the `A`-valued
inner product is given, for `x y : E × F`, `⟪x, y⟫_A := ⟪x.1, y.1⟫_A + ⟪x.2, y.2⟫_A`. The norm this
induces satisfies `‖x‖ ^ 2 = ‖⟪x.1, y.1⟫ + ⟪x.2, y.2⟫‖`, but this doesn't coincide with *any*
natural norm on `E × F` unless `A := ℂ`, in which case it is `WithLp 2 (E × F)` because `E × F` is
then an `InnerProductSpace` over `ℂ`.

## References

+ Erin Wittlich. *Formalizing Hilbert Modules in C⋆-algebras with the Lean Proof Assistant*,
  December 2022. Master's thesis, Southern Illinois University Edwardsville.
-/

open scoped ComplexOrder RightActions

class CStarModule (A E : Type*) [NonUnitalSemiring A] [StarRing A]
    [Module ℂ A] [AddCommGroup E] [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E]
    extends Inner A E where
  inner_add_right {x} {y} {z} : inner x (y + z) = inner x y + inner x z
  inner_self_nonneg {x} : 0 ≤ inner x x
  inner_self {x} : inner x x = 0 ↔ x = 0
  inner_op_smul_right {a : A} {x y : E} : inner x (a • y) = a * inner x y
  inner_smul_right_complex {z : ℂ} {x} {y} : inner x (z • y) = z • inner x y
  star_inner x y : star (inner x y) = inner y x
  norm_eq_sqrt_norm_inner_self x : ‖x‖ = √‖inner x x‖

attribute [simp] CStarModule.inner_add_right CStarModule.star_inner

  CStarModule.inner_op_smul_right CStarModule.inner_smul_right_complex

namespace CStarModule

section general

variable {A E : Type*} [NonUnitalRing A] [StarRing A] [AddCommGroup E] [Module ℂ A]
  [Module ℂ E] [PartialOrder A] [SMul A E] [Norm A] [Norm E] [CStarModule A E]

local notation "⟪" x ", " y "⟫" => inner A x y
