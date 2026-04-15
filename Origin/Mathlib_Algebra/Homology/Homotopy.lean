/-
Extracted from Algebra/Homology/Homotopy.lean
Genuine: 2 of 2 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Chain homotopies

We define chain homotopies, and prove that homotopic chain maps induce the same map on homology.
-/

universe v u

noncomputable section

open CategoryTheory Category Limits HomologicalComplex

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {c : ComplexShape ι} {C D E : HomologicalComplex V c}

variable (f g : C ⟶ D) (h k : D ⟶ E) (i : ι)

def dNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.X i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => C.d i (c.next i) ≫ f (c.next i) i) fun _ _ =>
    Preadditive.comp_add _ _ _ _ _ _

def fromNext (i : ι) : (∀ i j, C.X i ⟶ D.X j) →+ (C.xNext i ⟶ D.X i) :=
  AddMonoidHom.mk' (fun f => f (c.next i) i) fun _ _ => rfl
