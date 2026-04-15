/-
Extracted from CategoryTheory/Limits/Presentation.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# (Co)limit presentations

Let `J` and `C` be categories and `X : C`. We define type `ColimitPresentation J X` that contains
the data of objects `Dⱼ` and natural maps `sⱼ : Dⱼ ⟶ X` that make `X` the colimit of the `Dⱼ`.

(See `Mathlib/CategoryTheory/Presentable/ColimitPresentation.lean` for the construction of a
presentation of a colimit of objects that are equipped with presentations.)

## Main definitions:

- `CategoryTheory.Limits.ColimitPresentation`: A colimit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : Dᵢ ⟶ X` making `X` into the colimit of the `Dᵢ`.
- `CategoryTheory.Limits.LimitPresentation`: A limit presentation of `X` over `J` is a diagram
  `{Dᵢ}` in `C` and natural maps `sᵢ : X ⟶ Dᵢ` making `X` into the limit of the `Dᵢ`.

## TODOs:

- Refactor `TransfiniteCompositionOfShape` so that it extends `ColimitPresentation`.
-/

universe s t w v u

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

structure ColimitPresentation (J : Type w) [Category.{t} J] (X : C) where
  /-- The diagram `{Dᵢ}`. -/
  diag : J ⥤ C
  /-- The natural maps `sᵢ : Dᵢ ⟶ X`. -/
  ι : diag ⟶ (Functor.const J).obj X
  /-- `X` is the colimit of the `Dᵢ` via `sᵢ`. -/
  isColimit : IsColimit (Cocone.mk _ ι)

variable {J : Type w} [Category.{t} J] {X : C}

namespace ColimitPresentation

initialize_simps_projections ColimitPresentation (-isColimit)

set_option backward.isDefEq.respectTransparency false in
