/-
Extracted from CategoryTheory/Abelian/DiagramLemmas/KernelCokernelComp.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Long exact sequence for the kernel and cokernel of a composition

If `f : X ⟶ Y` and `g : Y ⟶ Z` are composable morphisms in an
abelian category, we construct a long exact sequence:
`0 ⟶ ker f ⟶ ker (f ≫ g) ⟶ ker g ⟶ coker f ⟶ coker (f ≫ g) ⟶ coker g ⟶ 0`.

This is obtained by applying the snake lemma to the following morphism of
exact sequences, where the rows are the obvious split exact sequences
```
0 ⟶ X ⟶ X ⊞ Y ⟶ Y ⟶ 0
    |f    |φ    |g
    v     v     v
0 ⟶ Y ⟶ Y ⊞ Z ⟶ Z ⟶ 0
```
and `φ` is given by the following matrix:
```
(f  -𝟙 Y)
(0     g)
```

Indeed the snake lemma gives an exact sequence involving the kernels and cokernels
of the vertical maps: in order to get the expected long exact sequence, it suffices
to obtain isomorphisms `ker φ ≅ ker (f ≫ g)` and `coker φ ≅ coker (f ≫ g)`.

-/

universe v u

namespace CategoryTheory

open Limits Category Preadditive

variable {C : Type u} [Category.{v} C] [Abelian C]
  {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)

namespace kernelCokernelCompSequence

noncomputable def ι : kernel (f ≫ g) ⟶ X ⊞ Y :=
  biprod.lift (kernel.ι (f ≫ g)) (kernel.ι (f ≫ g) ≫ f)
