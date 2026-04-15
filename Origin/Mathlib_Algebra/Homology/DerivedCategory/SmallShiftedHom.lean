/-
Extracted from Algebra/Homology/DerivedCategory/SmallShiftedHom.lean
Genuine: 1 of 2 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Cohomology of `HomComplex` and morphisms in the derived category

Let `K` and `L` be two cochain complexes in an abelian category `C`.
Given a class `x : HomComplex.CohomologyClass K L n`, we construct an
element in the type
`SmallShiftedHom (HomologicalComplex.quasiIso C (.up ℤ)) K L n`, and
compute its image as a morphism `Q.obj K ⟶ (Q.obj L)⟦n⟧` in the
derived category when `x` is given as the class of a cocycle.

-/

universe w v u

open CategoryTheory Localization

namespace CochainComplex.HomComplex.CohomologyClass

variable {C : Type u} [Category.{v} C] [Abelian C]
  {K L : CochainComplex C ℤ} {n : ℤ}
  [HasSmallLocalizedShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) ℤ K L]

set_option backward.isDefEq.respectTransparency false in

noncomputable def toSmallShiftedHom (x : CohomologyClass K L n) :
    SmallShiftedHom.{w} (HomologicalComplex.quasiIso C (.up ℤ)) K L n :=
  Quotient.lift (fun y ↦ SmallShiftedHom.mk _ (Cocycle.equivHomShift.symm y)) (by
    letI := HasDerivedCategory.standard C
    intro y₁ y₂ h
    refine (SmallShiftedHom.equiv _ DerivedCategory.Q).injective ?_
    simp only [SmallShiftedHom.equiv_mk, ShiftedHom.map]
    rw [cancel_mono, DerivedCategory.Q_map_eq_of_homotopy]
    apply HomotopyCategory.homotopyOfEq
    rw [← toHom_mk, ← toHom_mk]
    congr 1
    exact Quotient.sound h) x
