/-
Extracted from CategoryTheory/Monoidal/DayConvolution/DayFunctor.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Day functors

In this file, given a monoidal category `C` and a monoidal category `V`,
we define a basic type synonym `DayFunctor C V` (denoted `C ⊛⥤ D`)
for the category `C ⥤ V` and endow it with the monoidal structure coming
from Day convolution. Such a setup is necessary as by default,
the `MonoidalCategory` instance on `C ⥤ V` is the "pointwise" one,
where the tensor product of `F` and `G` is the functor `x ↦ F.obj x ⊗ G.obj x`.

## TODOs
- Given a `LawfulDayConvolutionMonoidalCategoryStruct C V D`, show that
  ι induces a monoidal functor `D ⥤ (C ⊛⥤ V)`.
- Specialize to the case `V := Type _`, and prove a universal property stating
  that for every monoidal category `W` with suitable colimits,
  colimit-preserving monoidal functors `(Cᵒᵖ ⊛⥤ Type u) ⥤ W` are equivalent to
  monoidal functors `C ⥤ W`. Show that the Yoneda embedding is monoidal.
-/

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryTheory.MonoidalCategory

open scoped ExternalProduct

noncomputable section

structure DayFunctor
    (C : Type u₁) [Category.{v₁} C] (V : Type u₂) [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V] where
  /-- the underlying functor. -/
  functor : C ⥤ V

namespace DayFunctor

scoped infixr:26 " ⊛⥤ " => DayFunctor

variable {C : Type u₁} [Category.{v₁} C] {V : Type u₂} [Category.{v₂} V]
    [MonoidalCategory C] [MonoidalCategory V]
