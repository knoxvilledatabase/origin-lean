/-
Extracted from CategoryTheory/Limits/Types/Equalizers.lean
Genuine: 5 of 5 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Equalizers in Type

The equalizer of a pair of maps `(g, h)` from `X` to `Y` is the subtype `{x : Y // g x = h x}`.

-/

universe v u

open CategoryTheory Limits ConcreteCategory

namespace CategoryTheory.Limits.Types

variable {X Y Z : Type u} (f : X ⟶ Y) {g h : Y ⟶ Z} (w : f ≫ g = f ≫ h)

noncomputable def typeEqualizerOfUnique (t : ∀ y : Y, g y = h y → ∃! x : X, f x = y) :
    IsLimit (Fork.ofι _ w) :=
  Fork.IsLimit.mk' _ fun s => by
    refine ⟨TypeCat.ofHom (fun i => ?_), ?_, ?_⟩
    · apply Classical.choose (t (s.ι i) _)
      apply congr_hom s.condition i
    · ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).1
    · intro m hm
      ext i
      exact (Classical.choose_spec (t (s.ι i) (congr_hom s.condition i))).2 _ (congr_hom hm i)

theorem unique_of_type_equalizer (t : IsLimit (Fork.ofι _ w)) (y : Y) (hy : g y = h y) :
    ∃! x : X, f x = y := by
  let y' : PUnit ⟶ Y := TypeCat.ofHom (fun _ => y)
  have hy' : y' ≫ g = y' ≫ h := by ext; exact hy
  refine ⟨(Fork.IsLimit.lift' t _ hy').1 ⟨⟩, congr_hom (Fork.IsLimit.lift' t y' _).2 ⟨⟩, ?_⟩
  intro x' hx'
  suffices (fun _ : PUnit => x') = (Fork.IsLimit.lift' t y' hy').1 by
    rw [← this]
  apply TypeCat.homEquiv.symm.injective
  apply Fork.IsLimit.hom_ext t
  ext ⟨⟩
  apply hx'.trans (congr_hom (Fork.IsLimit.lift' t _ hy').2 ⟨⟩).symm

theorem type_equalizer_iff_unique :
    Nonempty (IsLimit (Fork.ofι _ w)) ↔ ∀ y : Y, g y = h y → ∃! x : X, f x = y :=
  ⟨fun i => unique_of_type_equalizer _ _ (Classical.choice i), fun k =>
    ⟨typeEqualizerOfUnique f w k⟩⟩

def equalizerLimit : Limits.LimitCone (parallelPair g h) where
  cone := Fork.ofι (TypeCat.ofHom (Subtype.val : { x : Y // g x = h x } → Y))
    (by ext x; exact x.prop)
  isLimit :=
    Fork.IsLimit.mk' _ fun s =>
      ⟨TypeCat.ofHom fun i => ⟨s.ι i, by apply congr_hom s.condition i⟩, rfl, fun hm =>
        by ext x; exact Subtype.ext (by exact congr_hom hm x)⟩

variable (g h)

noncomputable def equalizerIso : equalizer g h ≅ { x : Y // g x = h x } :=
  limit.isoLimitCone equalizerLimit
