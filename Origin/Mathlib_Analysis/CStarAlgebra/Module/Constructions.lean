/-
Extracted from Analysis/CStarAlgebra/Module/Constructions.lean
Genuine: 4 of 10 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-! # Constructions of Hilbert C⋆-modules

In this file we define the following constructions of `CStarModule`s where `A` denotes a C⋆-algebra.
For some of the types listed below, the instance is declared on the type synonym `WithCStarModule E`
(with the notation `C⋆ᵐᵒᵈ E`), instead of on `E` itself; we explain the reasoning behind each
decision below.

1. `A` as a `CStarModule` over itself.
2. `C⋆ᵐᵒᵈ(A, E × F)` as a `CStarModule` over `A`, when `E` and `F` are themselves `CStarModule`s
  over `A`.
3. `C⋆ᵐᵒᵈ (A, Π i : ι, E i)` as a `CStarModule` over `A`, when each `E i` is a `CStarModule` over
  `A` and `ι` is a `Fintype`.
4. `E` as a `CStarModule` over `ℂ`, when `E` is an `InnerProductSpace` over `ℂ`.

For `E × F` and `Π i : ι, E i`, we are required to declare the instance on a type synonym rather
than on the product or pi-type itself because the existing norm on these types does not agree with
the one induced by the C⋆-module structure. Moreover, the norm induced by the C⋆-module structure
doesn't agree with any other natural norm on these types (e.g., `WithLp 2 (E × F)` unless `A := ℂ`),
so we need a new synonym.

On `A` (a C⋆-algebra) and `E` (an inner product space), we declare the instances on the types
themselves to ease the use of the C⋆-module structure. This does have the potential to cause
inconvenience (as sometimes Lean will see terms of type `A` and apply lemmas pertaining to
C⋆-modules to those terms, when the lemmas were actually intended for terms of some other
C⋆-module in context, say `F`, in which case the arguments must be provided explicitly; see for
instance the application of `CStarModule.norm_eq_sqrt_norm_inner_self` in the proof of
`WithCStarModule.max_le_prod_norm` below). However, we believe that this, hopefully rare,
inconvenience is outweighed by avoiding translating between type synonyms where possible.

For more details on the importance of the `WithCStarModule` type synonym, see the module
documentation for `Analysis.CStarAlgebra.Module.Synonym`.

## Implementation notes

When `A := ℂ` and `E := ℂ`, then `ℂ` is both a C⋆-algebra (so it inherits a `CStarModule` instance
via (1) above) and an inner product space (so it inherits a `CStarModule` instance via (4) above).
We provide a sanity check ensuring that these two instances are definitionally equal. We also ensure
that the `Inner ℂ ℂ` instance from `InnerProductSpace` is definitionally equal to the one inherited
from the `CStarModule` instances.

Note that `C⋆ᵐᵒᵈ(A, E)` is *already* equipped with a bornology and uniformity whenever `E` is
(namely, the pullback of the respective structures through `WithCStarModule.equiv`), so in each of
the above cases, it is necessary to temporarily instantiate `C⋆ᵐᵒᵈ(A, E)` with
`CStarModule.normedAddCommGroup`, show the resulting type is bilipschitz equivalent to `E` via
`WithCStarModule.equiv` (in the first and last case, this map is actually trivially an isometry),
and then replace the uniformity and bornology with the correct ones.

-/

open CStarModule CStarRing

namespace WithCStarModule

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A]

/-! ## A C⋆-algebra as a C⋆-module over itself -/

section Self

variable [StarOrderedRing A]

-- INSTANCE (free from Core): :

open scoped InnerProductSpace in

end Self

/-! ## Products of C⋆-modules -/

section Prod

open scoped InnerProductSpace

variable {E F : Type*}

variable [NormedAddCommGroup E] [Module ℂ E] [SMul A E]

variable [NormedAddCommGroup F] [Module ℂ F] [SMul A F]

variable [CStarModule A E] [CStarModule A F]

-- INSTANCE (free from Core): :

lemma prod_norm_sq (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ^ 2 = ‖⟪x.1, x.1⟫_A + ⟪x.2, x.2⟫_A‖ := by
  simp [prod_norm]

lemma prod_norm_le_norm_add (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖x‖ ≤ ‖x.1‖ + ‖x.2‖ := by
  refine abs_le_of_sq_le_sq' ?_ (by positivity) |>.2
  calc ‖x‖ ^ 2 ≤ ‖⟪x.1, x.1⟫_A‖ + ‖⟪x.2, x.2⟫_A‖ := prod_norm_sq x ▸ norm_add_le _ _
    _ = ‖x.1‖ ^ 2 + 0 + ‖x.2‖ ^ 2 := by simp [norm_sq_eq A]
    _ ≤ ‖x.1‖ ^ 2 + 2 * ‖x.1‖ * ‖x.2‖ + ‖x.2‖ ^ 2 := by gcongr; positivity
    _ = (‖x.1‖ + ‖x.2‖) ^ 2 := by ring

variable [StarOrderedRing A]

-- INSTANCE (free from Core): :

lemma max_le_prod_norm (x : C⋆ᵐᵒᵈ(A, E × F)) : max ‖x.1‖ ‖x.2‖ ≤ ‖x‖ := by
  rw [prod_norm]
  simp only [norm_eq_sqrt_norm_inner_self (A := A) (E := E),
    norm_eq_sqrt_norm_inner_self (A := A) (E := F), max_le_iff, norm_nonneg,
    Real.sqrt_le_sqrt_iff]
  constructor
  all_goals
    refine CStarAlgebra.norm_le_norm_of_nonneg_of_le (A := A) ?_ ?_
    all_goals
      aesop (add safe apply CStarModule.inner_self_nonneg)

lemma norm_equiv_le_norm_prod (x : C⋆ᵐᵒᵈ(A, E × F)) : ‖equiv A (E × F) x‖ ≤ ‖x‖ :=
  max_le_prod_norm x

section Aux

attribute [-instance] WithCStarModule.instUniformSpace WithCStarModule.instBornology
