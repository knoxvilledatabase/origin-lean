/-
Extracted from Analysis/Calculus/VectorField.lean
Genuine: 2 of 4 | Dissolved: 0 | Infrastructure: 2
-/
import Origin.Core

/-!
# Vector fields in vector spaces

We study functions of the form `V : E → E` on a vector space, thinking of these as vector fields.
We define several notions in this context, with the aim to generalize them to vector fields on
manifolds.

Notably, we define the pullback of a vector field under a map, as
`VectorField.pullback 𝕜 f V x := (fderiv 𝕜 f x).inverse (V (f x))` (together with the same notion
within a set).

We also define the Lie bracket of two vector fields as
`VectorField.lieBracket 𝕜 V W x := fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)`
(together with the same notion within a set).

In addition to comprehensive API on these two notions, the main results are the following:
* `VectorField.pullback_lieBracket` states that the pullback of the Lie bracket
  is the Lie bracket of the pullbacks, when the second derivative is symmetric.
* `VectorField.leibniz_identity_lieBracket` is the Leibniz
  identity `[U, [V, W]] = [[U, V], W] + [V, [U, W]]`.

-/

open Set

open scoped Topology

noncomputable section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {n : WithTop ℕ∞}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {V W V₁ W₁ : E → E} {s t : Set E} {x : E}

/-!
### The Lie bracket of vector fields in a vector space

We define the Lie bracket of two vector fields, and call it `lieBracket 𝕜 V W x`. We also define
a version localized to sets, `lieBracketWithin 𝕜 V W s x`. We copy the relevant API
of `fderivWithin` and `fderiv` for these notions to get a comprehensive API.
-/

namespace VectorField

variable (𝕜) in

def lieBracket (V W : E → E) (x : E) : E :=
  fderiv 𝕜 W x (V x) - fderiv 𝕜 V x (W x)

variable (𝕜) in

def lieBracketWithin (V W : E → E) (s : Set E) (x : E) : E :=
  fderivWithin 𝕜 W s x (V x) - fderivWithin 𝕜 V s x (W x)
