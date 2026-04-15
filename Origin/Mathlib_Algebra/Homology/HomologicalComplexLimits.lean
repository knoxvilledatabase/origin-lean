/-
Extracted from Algebra/Homology/HomologicalComplexLimits.lean
Genuine: 1 of 1 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!
# Limits and colimits in the category of homological complexes

In this file, it is shown that if a category `C` has (co)limits of shape `J`,
then it is also the case of the categories `HomologicalComplex C c`,
and the evaluation functors `eval C c i : HomologicalComplex C c ⥤ C`
commute to these.

-/

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι J : Type*} [Category* C] [Category* J] {c : ComplexShape ι} [HasZeroMorphisms C]

variable (F : J ⥤ HomologicalComplex C c)

set_option backward.isDefEq.respectTransparency false in

def isLimitOfEval (s : Cone F)
    (hs : ∀ (i : ι), IsLimit ((eval C c i).mapCone s)) : IsLimit s where
  lift t :=
    { f := fun i => (hs i).lift ((eval C c i).mapCone t)
      comm' := fun i i' _ => by
        apply IsLimit.hom_ext (hs i')
        intro j
        have eq := fun k => (hs k).fac ((eval C c k).mapCone t)
        simp only [Functor.mapCone_π_app, eval_map] at eq
        simp only [Functor.mapCone_π_app, eval_map, assoc]
        rw [eq i', ← Hom.comm, reassoc_of% (eq i), Hom.comm] }
  fac t j := by
    ext i
    apply (hs i).fac
  uniq t m hm := by
    ext i
    apply (hs i).uniq ((eval C c i).mapCone t)
    intro j
    dsimp
    simp only [← comp_f, hm]

variable [∀ (n : ι), HasLimit (F ⋙ eval C c n)]

set_option backward.isDefEq.respectTransparency false in
