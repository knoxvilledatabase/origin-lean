/-
Extracted from CategoryTheory/SmallObject/WellOrderInductionData.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits of inverse systems indexed by well-ordered types

Given a functor `F : Jᵒᵖ ⥤ Type v` where `J` is a well-ordered type,
we introduce a structure `F.WellOrderInductionData` which allows
to show that the map `F.sections → F.obj (op ⊥)` is surjective.

The data and properties in `F.WellOrderInductionData` consist of a
section to the maps `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal,
and, when `j` is limit, a section to the canonical map from `F.obj (op j)`
to the type of compatible families of elements in `F.obj (op i)` for `i < j`.

In other words, from `val₀ : F.obj (op ⊥)`, a term `d : F.WellOrderInductionData`
allows the construction, by transfinite induction, of a section of `F`
which restricts to `val₀`.

-/

universe v u

namespace CategoryTheory

open Opposite

namespace Functor

variable {J : Type u} [LinearOrder J] [SuccOrder J] (F : Jᵒᵖ ⥤ Type v)

structure WellOrderInductionData where
  /-- A section `F.obj (op j) → F.obj (op (Order.succ j))` to the restriction
  `F.obj (op (Order.succ j)) → F.obj (op j)` when `j` is not maximal. -/
  succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) : F.obj (op (Order.succ j))
  map_succ (j : J) (hj : ¬IsMax j) (x : F.obj (op j)) :
      F.map (homOfLE (Order.le_succ j)).op (succ j hj x) = x
  /-- When `j` is a limit element, and `x` is a compatible family of elements
  in `F.obj (op i)` for all `i < j`, this is a lifting to `F.obj (op j)`. -/
  lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections) :
      F.obj (op j)
  map_lift (j : J) (hj : Order.IsSuccLimit j)
    (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections)
    (i : J) (hi : i < j) :
        F.map (homOfLE hi.le).op (lift j hj x) = x.val (op ⟨i, hi⟩)

namespace WellOrderInductionData

variable {F} in

noncomputable def ofExists
    (h₁ : ∀ (j : J) (_ : ¬IsMax j), Function.Surjective (F.map (homOfLE (Order.le_succ j)).op))
    (h₂ : ∀ (j : J) (_ : Order.IsSuccLimit j)
      (x : ((OrderHom.Subtype.val (· ∈ Set.Iio j)).monotone.functor.op ⋙ F).sections),
      ∃ (y : F.obj (op j)), ∀ (i : J) (hi : i < j),
        F.map (homOfLE hi.le).op y = x.val (op ⟨i, hi⟩)) :
    F.WellOrderInductionData where
  succ j hj x := (h₁ j hj x).choose
  map_succ j hj x := (h₁ j hj x).choose_spec
  lift j hj x := (h₂ j hj x).choose
  map_lift j hj x := (h₂ j hj x).choose_spec

variable {F} (d : F.WellOrderInductionData) [OrderBot J]

set_option backward.isDefEq.respectTransparency false in

structure Extension (val₀ : F.obj (op ⊥)) (j : J) where
  /-- An element in `F.obj (op j)`, which, by restriction, induces elements
  in `F.obj (op i)` for all `i ≤ j`. -/
  val : F.obj (op j)
  map_zero : F.map (homOfLE bot_le).op val = val₀
  map_succ (i : J) (hi : i < j) :
    F.map (homOfLE (Order.succ_le_of_lt hi)).op val =
      d.succ i (not_isMax_iff.2 ⟨_, hi⟩) (F.map (homOfLE hi.le).op val)
  map_limit (i : J) (hi : Order.IsSuccLimit i) (hij : i ≤ j) :
    F.map (homOfLE hij).op val = d.lift i hi
      { val := fun ⟨⟨k, hk⟩⟩ ↦ F.map (homOfLE (hk.le.trans hij)).op val
        property := fun f ↦ by
          dsimp
          rw [← comp_apply, ← map_comp]
          rfl }

namespace Extension

variable {d} {val₀ : F.obj (op ⊥)}
