/-
Extracted from Algebra/Homology/HomologicalComplex.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homological complexes.

A `HomologicalComplex V c` with a "shape" controlled by `c : ComplexShape ι`
has chain groups `X i` (objects in `V`) indexed by `i : ι`,
and a differential `d i j` whenever `c.Rel i j`.

We in fact ask for differentials `d i j` for all `i j : ι`,
but have a field `shape` requiring that these are zero when not allowed by `c`.
This avoids a lot of dependent type theory hell!

The composite of any two differentials `d i j ≫ d j k` must be zero.

We provide `ChainComplex V α` for
`α`-indexed chain complexes in which `d i j ≠ 0` only if `j + 1 = i`,
and similarly `CochainComplex V α`, with `i = j + 1`.

There is a category structure, where morphisms are chain maps.

For `C : HomologicalComplex V c`, we define `C.xNext i`, which is either `C.X j` for some
arbitrarily chosen `j` such that `c.r i j`, or `C.X i` if there is no such `j`.
Similarly we have `C.xPrev j`.
Defined in terms of these we have `C.dFrom i : C.X i ⟶ C.xNext i` and
`C.dTo j : C.xPrev j ⟶ C.X j`, which are either defined as `C.d i j`, or zero, as needed.
-/

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

variable {ι : Type*}

variable (V : Type u) [Category.{v} V] [HasZeroMorphisms V]

structure HomologicalComplex (c : ComplexShape ι) where
  X : ι → V
  d : ∀ i j, X i ⟶ X j
  shape : ∀ i j, ¬c.Rel i j → d i j = 0 := by cat_disch
  d_comp_d' : ∀ i j k, c.Rel i j → c.Rel j k → d i j ≫ d j k = 0 := by cat_disch

namespace HomologicalComplex

attribute [simp] shape

variable {V} {c : ComplexShape ι}
