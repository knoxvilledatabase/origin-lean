/-
Extracted from Algebra/Lie/TraceForm.lean
Genuine: 3 of 4 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# The trace and Killing forms of a Lie algebra.

Let `L` be a Lie algebra with coefficients in a commutative ring `R`. Suppose `M` is a finite, free
`R`-module and we have a representation `φ : L → End M`. This data induces a natural bilinear form
`B` on `L`, called the trace form associated to `M`; it is defined as `B(x, y) = Tr (φ x) (φ y)`.

In the special case that `M` is `L` itself and `φ` is the adjoint representation, the trace form
is known as the Killing form.

We define the trace / Killing form in this file and prove some basic properties.

## Main definitions

* `LieModule.traceForm`: a finite, free representation of a Lie algebra `L` induces a bilinear form
  on `L` called the trace form.
* `LieModule.traceForm_eq_zero_of_isNilpotent`: the trace form induced by a nilpotent
  representation of a Lie algebra vanishes.
* `killingForm`: the adjoint representation of a (finite, free) Lie algebra `L` induces a bilinear
  form on `L` via the trace form construction.
-/

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "φ" => LieModule.toEnd R L M

open LinearMap (trace)

open Set Module

namespace LieModule

noncomputable def traceForm : LinearMap.BilinForm R L :=
  ((LinearMap.mul _ _).compl₁₂ (φ).toLinearMap (φ).toLinearMap).compr₂ (trace R M)

lemma traceForm_comm (x y : L) : traceForm R L M x y = traceForm R L M y x :=
  LinearMap.trace_mul_comm R (φ x) (φ y)

lemma traceForm_isSymm : LinearMap.IsSymm (traceForm R L M) := ⟨LieModule.traceForm_comm R L M⟩
