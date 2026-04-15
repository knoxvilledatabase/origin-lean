/-
Extracted from Algebra/Homology/ConcreteCategory.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Homology of complexes in concrete categories

The homology of short complexes in concrete categories was studied in
`Mathlib/Algebra/Homology/ShortComplex/ConcreteCategory.lean`. In this file,
we introduce specific definitions and lemmas for the homology
of homological complexes in concrete categories. In particular,
we give a computation of the connecting homomorphism of
the homology sequence in terms of (co)cycles.

-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type v}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory.{v} C FC] [HasForget₂ C Ab.{v}]
  [Abelian C] [(forget₂ C Ab).Additive] [(forget₂ C Ab).PreservesHomology]
  {ι : Type*} {c : ComplexShape ι}

namespace HomologicalComplex

variable (K : HomologicalComplex C c)

noncomputable def cyclesMk {i : ι} (x : (forget₂ C Ab).obj (K.X i)) (j : ι) (hj : c.next i = j)
    (hx : ((forget₂ C Ab).map (K.d i j)) x = 0) :
    (forget₂ C Ab).obj (K.cycles i) :=
  (K.sc i).cyclesMk x (by subst hj; exact hx)
