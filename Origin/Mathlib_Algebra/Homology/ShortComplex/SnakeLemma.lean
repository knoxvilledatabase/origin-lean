/-
Extracted from Algebra/Homology/ShortComplex/SnakeLemma.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# The snake lemma

The snake lemma is a standard tool in homological algebra. The basic situation
is when we have a diagram as follows in an abelian category `C`, with exact rows:

    L₁.X₁ ⟶ L₁.X₂ ⟶ L₁.X₃ ⟶ 0
      |       |       |
      |v₁₂.τ₁ |v₁₂.τ₂ |v₁₂.τ₃
      v       v       v
0 ⟶ L₂.X₁ ⟶ L₂.X₂ ⟶ L₂.X₃

We shall think of this diagram as the datum of a morphism `v₁₂ : L₁ ⟶ L₂` in the
category `ShortComplex C` such that both `L₁` and `L₂` are exact, and `L₁.g` is epi
and `L₂.f` is a mono (which is equivalent to saying that `L₁.X₃` is the cokernel
of `L₁.f` and `L₂.X₁` is the kernel of `L₂.g`). Then, we may introduce the kernels
and cokernels of the vertical maps. In other words, we may introduce short complexes
`L₀` and `L₃` that are respectively the kernel and the cokernel of `v₁₂`. All these
data constitute a `SnakeInput C`.

Given such a `S : SnakeInput C`, we define a connecting homomorphism
`S.δ : L₀.X₃ ⟶ L₃.X₁` and show that it is part of an exact sequence
`L₀.X₁ ⟶ L₀.X₂ ⟶ L₀.X₃ ⟶ L₃.X₁ ⟶ L₃.X₂ ⟶ L₃.X₃`. Each of the four exactness
statement is first stated separately as lemmas `L₀_exact`, `L₁'_exact`,
`L₂'_exact` and `L₃_exact` and the full 6-term exact sequence is stated
as `snake_lemma`. This sequence can even be extended with an extra `0`
on the left (see `mono_L₀_f`) if `L₁.X₁ ⟶ L₁.X₂` is a mono (i.e. `L₁` is short exact),
and similarly an extra `0` can be added on the right (`epi_L₃_g`)
if `L₂.X₂ ⟶ L₂.X₃` is an epi (i.e. `L₂` is short exact).

These results were also obtained in the Liquid Tensor Experiment. The code and the proof
here are slightly easier because of the use of the category `ShortComplex C`,
the use of duality (which allows to construct only half of the sequence, and deducing
the other half by arguing in the opposite category), and the use of "refinements"
(see `CategoryTheory.Abelian.Refinements`) instead of a weak form of pseudo-elements.

-/

namespace CategoryTheory

open Category Limits Preadditive

variable (C : Type*) [Category* C] [Abelian C]

namespace ShortComplex

structure SnakeInput where
  /-- the zeroth row -/
  L₀ : ShortComplex C
  /-- the first row -/
  L₁ : ShortComplex C
  /-- the second row -/
  L₂ : ShortComplex C
  /-- the third row -/
  L₃ : ShortComplex C
  /-- the morphism from the zeroth row to the first row -/
  v₀₁ : L₀ ⟶ L₁
  /-- the morphism from the first row to the second row -/
  v₁₂ : L₁ ⟶ L₂
  /-- the morphism from the second row to the third row -/
  v₂₃ : L₂ ⟶ L₃
  w₀₂ : v₀₁ ≫ v₁₂ = 0 := by cat_disch
  w₁₃ : v₁₂ ≫ v₂₃ = 0 := by cat_disch
  /-- `L₀` is the kernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₀ : IsLimit (KernelFork.ofι _ w₀₂)
  /-- `L₃` is the cokernel of `v₁₂ : L₁ ⟶ L₂`. -/
  h₃ : IsColimit (CokernelCofork.ofπ _ w₁₃)
  L₁_exact : L₁.Exact
  epi_L₁_g : Epi L₁.g
  L₂_exact : L₂.Exact
  mono_L₂_f : Mono L₂.f

initialize_simps_projections SnakeInput (-h₀, -h₃)

namespace SnakeInput

attribute [reassoc (attr := simp)] w₀₂ w₁₃

attribute [instance] epi_L₁_g

attribute [instance] mono_L₂_f

variable {C}

variable (S : SnakeInput C)
