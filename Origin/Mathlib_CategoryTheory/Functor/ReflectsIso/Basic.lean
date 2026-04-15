/-
Extracted from CategoryTheory/Functor/ReflectsIso/Basic.lean
Genuine: 7 of 10 | Dissolved: 0 | Infrastructure: 3
-/
import Origin.Core

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop`-valued typeclass `ReflectsIsomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/

namespace CategoryTheory

open Functor

variable {C : Type*} [Category* C]
  {D : Type*} [Category* D]
  {E : Type*} [Category* E]

section ReflectsIso

class Functor.ReflectsIsomorphisms (F : C ⥤ D) : Prop where
  /-- For any `f`, if `F.map f` is an iso, then so was `f`. -/
  reflects : ∀ {A B : C} (f : A ⟶ B) [IsIso (F.map f)], IsIso f

attribute [to_dual self] Functor.ReflectsIsomorphisms.reflects Functor.ReflectsIsomorphisms.mk

theorem isIso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [IsIso (F.map f)]
    [F.ReflectsIsomorphisms] : IsIso f :=
  ReflectsIsomorphisms.reflects F f

lemma isIso_iff_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    IsIso (F.map f) ↔ IsIso f :=
  ⟨fun _ => isIso_of_reflects_iso f F, fun _ => inferInstance⟩

lemma Functor.FullyFaithful.reflectsIsomorphisms {F : C ⥤ D} (hF : F.FullyFaithful) :
    F.ReflectsIsomorphisms where
  reflects _ _ := hF.isIso_of_isIso_map _

-- INSTANCE (free from Core): (priority

-- INSTANCE (free from Core): reflectsIsomorphisms_comp

lemma reflectsIsomorphisms_of_comp (F : C ⥤ D) (G : D ⥤ E)
    [(F ⋙ G).ReflectsIsomorphisms] : F.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ (F ⋙ G)]
    dsimp
    infer_instance

-- INSTANCE (free from Core): (F

lemma reflectsIsomorphisms_of_iso {F G : C ⥤ D} (α : F ≅ G) [F.ReflectsIsomorphisms] :
    G.ReflectsIsomorphisms where
  reflects f _ := by
    rw [← isIso_iff_of_reflects_iso _ F, ← NatIso.naturality_2 α f]
    infer_instance

lemma reflectsIsomorphisms_iso_iff {F G : C ⥤ D} (α : F ≅ G) :
    F.ReflectsIsomorphisms ↔ G.ReflectsIsomorphisms :=
  ⟨fun _ => reflectsIsomorphisms_of_iso α,
  fun _ => reflectsIsomorphisms_of_iso α.symm⟩

end ReflectsIso

end CategoryTheory
