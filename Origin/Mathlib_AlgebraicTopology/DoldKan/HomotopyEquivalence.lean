/-
Extracted from AlgebraicTopology/DoldKan/HomotopyEquivalence.lean
Genuine: 3 of 3 | Dissolved: 0 | Infrastructure: 0
-/
import Origin.Core

/-!

# The normalized Moore complex and the alternating face map complex are homotopy equivalent

In this file, when the category `A` is abelian, we obtain the homotopy equivalence
`homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex` between the
normalized Moore complex and the alternating face map complex of a simplicial object in `A`.

-/

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

  CategoryTheory.Preadditive Simplicial DoldKan

noncomputable section

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (X : SimplicialObject C)

noncomputable def homotopyPToId : ∀ q : ℕ, Homotopy (P q : K[X] ⟶ _) (𝟙 _)
  | 0 => Homotopy.refl _
  | q + 1 => by
    refine
      Homotopy.trans (Homotopy.ofEq ?_)
        (Homotopy.trans
          (Homotopy.add (homotopyPToId q) (Homotopy.compLeft (homotopyHσToZero q) (P q)))
          (Homotopy.ofEq ?_))
    · simp only [P_succ, comp_add, comp_id]
    · simp only [add_zero, comp_zero]

def homotopyQToZero (q : ℕ) : Homotopy (Q q : K[X] ⟶ _) 0 :=
  Homotopy.equivSubZero.toFun (homotopyPToId X q).symm

set_option backward.isDefEq.respectTransparency false in

theorem homotopyPToId_eventually_constant {q n : ℕ} (hqn : n < q) :
    ((homotopyPToId X (q + 1)).hom n (n + 1) : X _⦋n⦌ ⟶ X _⦋n + 1⦌) =
      (homotopyPToId X q).hom n (n + 1) := by
  simp only [homotopyHσToZero, AlternatingFaceMapComplex.obj_X, Homotopy.trans_hom,
    Homotopy.ofEq_hom, Pi.zero_apply, Homotopy.add_hom, Homotopy.compLeft_hom, add_zero,
    Homotopy.nullHomotopy'_hom, ComplexShape.down_Rel, hσ'_eq_zero hqn (c_mk (n + 1) n rfl),
    dite_eq_ite, ite_self, comp_zero, zero_add, homotopyPToId]
