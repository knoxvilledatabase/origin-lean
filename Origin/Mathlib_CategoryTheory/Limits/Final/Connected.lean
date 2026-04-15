/-
Extracted from CategoryTheory/Limits/Final/Connected.lean
Genuine: 2 of 8 | Dissolved: 0 | Infrastructure: 6
-/
import Origin.Core

/-!
# Characterization of connected categories using initial/final functors

A category `C` is connected iff the constant functor `C ⥤ Discrete PUnit`
is final (or initial).

We deduce that the projection `C × D ⥤ C` is final (or initial) if `D` is connected.

-/

universe w v v' u u'

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  {T : Type w} [Unique T]

lemma isConnected_iff_final_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Final := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.structuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

lemma isConnected_iff_initial_of_unique (F : C ⥤ Discrete T) :
    IsConnected C ↔ F.Initial := by
  rw [← isConnected_iff_of_equivalence
    (Discrete.costructuredArrowEquivalenceOfUnique F default)]
  refine ⟨fun _ ↦ ⟨?_⟩, fun _ ↦ inferInstance⟩
  rintro ⟨d⟩
  obtain rfl := Subsingleton.elim d default
  infer_instance

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): (F

-- INSTANCE (free from Core): final_fst

-- INSTANCE (free from Core): final_snd

-- INSTANCE (free from Core): initial_fst

-- INSTANCE (free from Core): initial_snd

end CategoryTheory
