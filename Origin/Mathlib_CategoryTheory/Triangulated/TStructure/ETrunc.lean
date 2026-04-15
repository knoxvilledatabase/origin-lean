/-
Extracted from CategoryTheory/Triangulated/TStructure/ETrunc.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Truncations for a t-structure

Let `t` be a t-structure on a triangulated category `C`.
In this file, we extend the definition of the truncation functors
`truncLT` and `truncGE` for indices in `ℤ` to `EInt`,
as `t.eTruncLT : EInt ⥤ C ⥤ C` and `t.eTruncGE : EInt ⥤ C ⥤ C`.

-/

namespace CategoryTheory

open Category Limits Pretriangulated ZeroObject Preadditive

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

namespace Triangulated

namespace TStructure

variable (t : TStructure C)

noncomputable def eTruncLT : EInt ⥤ C ⥤ C where
  obj := WithBotTop.rec 0 t.truncLT (𝟭 C)
  map {x y} f := by
    induction x using WithBotTop.rec with
    | bot =>
      induction y using WithBotTop.rec with
      | bot => exact 𝟙 _
      | coe b => exact 0
      | top => exact 0
    | coe a =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact t.natTransTruncLTOfLE a b (by simpa using leOfHom f)
      | top => exact t.truncLTι a
    | top =>
      induction y using WithBotTop.rec with
      | bot => exact 0
      | coe b => exact 0
      | top => exact 𝟙 _
  map_id n := by induction n using WithBotTop.rec <;> simp
  map_comp {x y z} f g := by
    have f' := leOfHom f
    have g' := leOfHom g
    induction x using WithBotTop.rec <;> induction y using WithBotTop.rec <;>
      induction z using WithBotTop.rec <;> cat_disch
