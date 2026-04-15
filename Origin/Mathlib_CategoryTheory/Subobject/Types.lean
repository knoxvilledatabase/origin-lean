/-
Extracted from CategoryTheory/Subobject/Types.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# `Type u` is well-powered

By building a categorical equivalence `MonoOver α ≌ Set α` for any `α : Type u`,
we deduce that `Subobject α ≃o Set α` and that `Type u` is well-powered.

One would hope that for a particular concrete category `C` (`AddCommGroup`, etc)
it's viable to prove `[WellPowered C]` without explicitly aligning `Subobject X`
with the "hand-rolled" definition of subobjects.

This may be possible using Lawvere theories,
but it remains to be seen whether this just pushes lumps around in the carpet.
-/

universe u

open CategoryTheory ConcreteCategory

open CategoryTheory.Subobject

theorem subtype_val_mono {α : Type u} (s : Set α) : Mono (TypeCat.ofHom (Subtype.val : s → α)) :=
  (mono_iff_injective _).mpr Subtype.val_injective

attribute [local instance] subtype_val_mono
