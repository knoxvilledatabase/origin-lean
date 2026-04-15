/-
Extracted from AlgebraicTopology/SimplicialSet/SubcomplexColimits.lean
Genuine: 4 of 5 | Dissolved: 0 | Infrastructure: 1
-/
import Origin.Core

/-!
# Colimits involving subcomplexes of a simplicial set

If `X` is a simplicial set, and we have subcomplexes `A`, `U i` (for `i : ι`) and
`V i j` which satisfy `Subcomplex.MulticoequalizerDiagram A U V` (an abbreviation
for `CompleteLattice.MulticoequalizerDiagram`), we
show that the simplicial sset corresponding to `A` is the multicoequalizer of
the `U i` along the `V i j`.

Similarly, bicartesian squares in the lattice `Subcomplex X` give pushout
squares in the category of simplicial sets.

-/

universe u

open CategoryTheory Limits

namespace SSet

namespace Subcomplex

variable {X : SSet.{u}}

variable {A : X.Subcomplex} {ι : Type*}
  {U : ι → X.Subcomplex} {V : ι → ι → X.Subcomplex}

variable (A U V) in

abbrev MulticoequalizerDiagram := CompleteLattice.MulticoequalizerDiagram A U V

namespace MulticoequalizerDiagram

variable (h : MulticoequalizerDiagram A U V)

noncomputable def isColimit :
    IsColimit (h.multicofork.map toSSetFunctor) :=
  evaluationJointlyReflectsColimits _ (fun n ↦ by
    have h' : CompleteLattice.MulticoequalizerDiagram (A.obj n) (fun i ↦ (U i).obj n)
        (fun i j ↦ (V i j).obj n) :=
      { eq_inf := by simp [h.eq_inf]
        iSup_eq := by simp [← h.iSup_eq] }
    exact (Multicofork.isColimitMapEquiv _ _).2
      (Types.isColimitOfMulticoequalizerDiagram h'))

noncomputable def isColimit' [LinearOrder ι] :
    IsColimit (h.multicofork.toLinearOrder.map toSSetFunctor) :=
  Multicofork.isColimitToLinearOrder _ h.isColimit
    { iso i j := toSSetFunctor.mapIso (eqToIso (by
        dsimp
        rw [h.eq_inf, h.eq_inf, inf_comm]))
      iso_hom_fst _ _ := rfl
      iso_hom_snd _ _ := rfl
      fst_eq_snd _ := rfl }

end MulticoequalizerDiagram

end

abbrev BicartSq (A₁ A₂ A₃ A₄ : X.Subcomplex) := Lattice.BicartSq A₁ A₂ A₃ A₄

end Subcomplex

end SSet
