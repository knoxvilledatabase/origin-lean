/-
Extracted from Algebra/Homology/DifferentialObject.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homological complexes are differential graded objects.

We verify that a `HomologicalComplex` indexed by an `AddCommGroup` is
essentially the same thing as a differential graded object.

This equivalence is probably not particularly useful in practice;
it's here to check that definitions match up as expected.
-/

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-!
We first prove some results about differential graded objects.

TODO: We should move these to their own file.
-/

namespace CategoryTheory.DifferentialObject

variable {β : Type*} [AddCommGroup β] {b : β}

variable {V : Type*} [Category* V] [HasZeroMorphisms V]

variable (X : DifferentialObject ℤ (GradedObjectWithShift b V))

abbrev objEqToHom {i j : β} (h : i = j) :
    X.obj i ⟶ X.obj j :=
  eqToHom (congr_arg X.obj h)
