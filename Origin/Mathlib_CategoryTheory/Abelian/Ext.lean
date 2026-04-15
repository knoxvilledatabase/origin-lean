/-
Extracted from CategoryTheory/Abelian/Ext.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Ext

We define `Ext R C n : Cᵒᵖ ⥤ C ⥤ ModuleCat R` for any `R`-linear abelian category `C`
by (left) deriving in the first argument of the bifunctor `(X, Y) ↦ ModuleCat.of R (unop X ⟶ Y)`.

## Implementation

TODO (@joelriou): When the derived category enters mathlib, the Ext groups shall be
redefined using morphisms in the derived category, and then it will be possible to
compute `Ext` using both projective or injective resolutions.

-/

noncomputable section

open CategoryTheory Limits

variable (R : Type*) [Ring R] (C : Type*) [Category* C] [Abelian C] [Linear R C]
  [EnoughProjectives C]

def Ext (n : ℕ) : Cᵒᵖ ⥤ C ⥤ ModuleCat R :=
  Functor.flip
    { obj := fun Y => (((linearYoneda R C).obj Y).rightOp.leftDerived n).leftOp
      map := fun f => ((((linearYoneda R C).map f).rightOp).leftDerived n).leftOp }

open ZeroObject

variable {R C}
